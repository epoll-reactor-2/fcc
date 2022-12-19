/* Fuzzer.cpp - Valid weak language code programs generator and tester.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Lex/Lexer.h"
#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/Analysis/FunctionAnalysis.h"
#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "FrontEnd/Analysis/TypeAnalysis.h"
#include "MiddleEnd/CodeGen/CodeGen.h"
#include "MiddleEnd/Driver/Driver.h"
#include "MiddleEnd/Optimizers/Optimizers.h"
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <sstream>
#include <fstream>
#include <random>
#include <set>
#include <vector>

static const char *IntOperators[] = {
  "+",
  "-",
  "<<",
  ">>",
  "%",
  "/",
  "*",
  "|",
  "&",
  "^"
};

static const char *FloatOperators[] = {
  "+",
  "-",
  "*",
  "/"
};

static const char *BoolOperators[] = {
  "&&",
  "||",
  "==",
  "!=",
  ">",
  "<",
  ">=",
  "<="
};

static const char *DataTypes[] = {
  "int",
  "float",
  "char",
  "bool"
};

static char LettersSet[] = {
  'A','B','C','D','E','F',
  'G','H','I','J','K',
  'L','M','N','O','P',
  'Q','R','S','T','U',
  'V','W','X','Y','Z',
  'a','b','c','d','e','f',
  'g','h','i','j','k',
  'l','m','n','o','p',
  'q','r','s','t','u',
  'v','w','x','y','z'
};

std::default_random_engine RandomEngine(std::random_device{}());
std::uniform_real_distribution<float> FloatDistribution(0, 1);
std::uniform_int_distribution<> NumericDistribution(0, 674545);
std::uniform_int_distribution<> LetterDistribution(0, std::size(LettersSet) - 1);
std::uniform_int_distribution<> IntOperatorsDistribution(0, std::size(IntOperators) - 1);
std::uniform_int_distribution<> FloatOperatorsDistribution(0, std::size(FloatOperators) - 1);
std::uniform_int_distribution<> BoolOperatorsDistribution(0, std::size(BoolOperators) - 1);
std::uniform_int_distribution<> DataTypesDistribution(0, std::size(DataTypes) - 1);
std::uniform_int_distribution<> BooleanDistribution(0, 1);

struct VariableStackRecord {
  std::string Type, Name;
};

struct FunctionRecord {
  std::string ReturnType, Name;
  std::vector<std::string> ArgTypes;
};

std::vector<std::vector<VariableStackRecord>> VariablesStack(1);
std::vector<FunctionRecord> FunctionsStack;

signed RandomNumber() {
  return NumericDistribution(RandomEngine);
}

float RandomFloat() {
  return FloatDistribution(RandomEngine);
}

char RandomLetter() {
  return LettersSet[LetterDistribution(RandomEngine)];
}

bool RandomBool() {
  return BooleanDistribution(RandomEngine);
}

const char *RandomDataType() {
  return DataTypes[DataTypesDistribution(RandomEngine)];
}

const char *RandomIntOperator() {
  return IntOperators[IntOperatorsDistribution(RandomEngine)];
}

const char *RandomFloatOperator() {
  return FloatOperators[FloatOperatorsDistribution(RandomEngine)];
}

const char *RandomBoolOperator() {
  return BoolOperators[BoolOperatorsDistribution(RandomEngine)];
}

const VariableStackRecord &RandomVariable(size_t Index) {
  auto &R = VariablesStack.at(Index);

  std::uniform_int_distribution<> ScopeDistribution(0, R.size() - 1);
  Index = ScopeDistribution(RandomEngine);

  return R.at(Index);
}

const FunctionRecord &RandomFunction() {
  std::uniform_int_distribution<> FunctionDistribution(0, FunctionsStack.size() - 1);
  return FunctionsStack[FunctionDistribution(RandomEngine)];
}

std::string RandomString() {
  std::uniform_int_distribution<> LengthDistribution(10, 20);
  size_t Length = LengthDistribution(RandomEngine);
  std::string String(Length, 0);
  std::generate_n(String.begin(), Length, RandomLetter);
  return String;
}

std::ostream &CreateNum(std::ostream &S) {
  return S << RandomNumber();
}

std::ostream &CreateString(std::ostream &S) {
  return S << RandomString();
}

std::ostream &RandomUnary(std::ostream &S) {
  return S << (RandomBool() ? "++" : "--") << RandomNumber();
}

template <typename EmitterFn, typename RandomOperatorFn>
std::ostream &RandomBinaryGeneric(std::ostream &S, std::string_view Type, EmitterFn LiteralEmit, RandomOperatorFn RandomOperator) {
  std::uniform_int_distribution<> VariableDistribution(0, VariablesStack.size() - 1);
  size_t I = VariableDistribution(RandomEngine);

  if (VariablesStack.empty() || VariablesStack[I].empty())
    LiteralEmit();
  else
    if (const auto &Var = RandomVariable(I); Var.Type != Type)
      LiteralEmit();
    else
      S << Var.Name;
  S << RandomOperator();

  /// Increasing or decreasing `%` operand, we set
  /// average binary chain length.
  if (RandomNumber() % 10 == 0) {
    if (VariablesStack.empty() || VariablesStack[I].empty())
      return LiteralEmit();
    const auto &Var = RandomVariable(I);
    if (Var.Type != Type)
      return LiteralEmit();
    return S << Var.Name;
  }
  return RandomBinaryGeneric(S, Type, LiteralEmit, RandomOperator);
}

std::ostream &RandomBinary(std::string DT, std::ostream &S) {
  if (DT == "int")
    return RandomBinaryGeneric(S, DT, [&S]() -> std::ostream & { return S << RandomNumber(); }, RandomIntOperator);
  if (DT == "float")
    return RandomBinaryGeneric(S, DT, [&S]() -> std::ostream & { return S << std::fixed << RandomFloat(); }, RandomFloatOperator);
  if (DT == "bool")
    return RandomBinaryGeneric(S, DT, [&S]() -> std::ostream & { return S << (RandomBool() ? "true" : "false"); }, RandomBoolOperator);
  if (DT == "char")
    return S << RandomLetter();
  __builtin_trap();
}

std::ostream &RandomBoolBinary(std::ostream &S) {
  return RandomBinaryGeneric(S, "bool", [&S]() -> std::ostream & { return S << (RandomBool() ? "true" : "false"); }, RandomBoolOperator);
}

std::ostream &RandomVarDeclWithoutInitializer(std::ostream &S) {
  std::string Name = RandomString();
  std::string DT = RandomDataType();
  VariablesStack.back().emplace_back(VariableStackRecord{DT, Name});
  return S << DT << ' ' << Name;
}

std::ostream &RandomVarDecl(std::ostream &S) {
  std::string Name = RandomString();
  std::string DT = RandomDataType();

  if (DT == "int") {
    S << "int " << Name << " = ";
    RandomBinary(DT, S);
    S << ";";
  } else if (DT == "float") {
    S << "float " << Name << " = " << std::fixed << RandomFloat() << ";";
  } else if (DT == "char") {
    S << "char " << Name << " = '" << RandomLetter() << "';";
  } else if (DT == "bool") {
    S << "bool " << Name << " = " << (RandomBool() ? "true" : "false") << ";";
  }
  S << '\n';

  VariablesStack.back().emplace_back(VariableStackRecord{DT, Name});
  return S;
}

std::ostream &RandomBlock(std::ostream &S);

std::ostream &RandomWhile(std::ostream &S) {
  for (signed I = 5, Size = (RandomNumber() % 25) + I; I < Size; ++I)
    RandomVarDecl(S);
  S << "while (";
  RandomBoolBinary(S);
  S << ")\n";
  RandomBlock(S);
  return S;
}

std::ostream &RandomDoWhile(std::ostream &S) {
  for (signed I = 5, Size = (RandomNumber() % 25) + I; I < Size; ++I)
    RandomVarDecl(S);
  S << "do ";
  RandomBlock(S);
  S << " while (";
  RandomBoolBinary(S);
  return S << ");";
}

std::ostream &RandomFor(std::ostream &S) {
  for (signed I = 5, Size = (RandomNumber() % 25) + I; I < Size; ++I)
    RandomVarDecl(S);
  VariablesStack.push_back({});
  S << "for (";
  RandomVarDecl(S); /// `;` already there.
  RandomBoolBinary(S);
  S << "; ";
  RandomBinary("int", S);
  S << ")\n";
  RandomBlock(S);
  VariablesStack.pop_back();
  return S;
}

std::ostream &RandomIf(std::ostream &S) {
  for (signed I = 5, Size = (RandomNumber() % 25) + I; I < Size; ++I)
    RandomVarDecl(S);
  S << "if (";
  RandomBoolBinary(S);
  S << ")\n";
  RandomBlock(S);
  if (RandomBool()) {
    S << " else ";
    RandomBlock(S);
  }
  return S;
}

std::ostream &RandomFunctionCall(std::ostream &S) {
  if (FunctionsStack.empty())
    return S;

  const auto &F = RandomFunction();
  S << F.Name << "(";

  for (signed I = 0, Size = F.ArgTypes.size(); I < Size; ++I) {
    std::uniform_int_distribution<> VariableDistribution(0, VariablesStack.size() - 1);
    size_t StackIndex = VariableDistribution(RandomEngine);

    auto EmitValue = [&](std::string_view Type, auto LiteralFn) mutable {
      if (VariablesStack.empty() || VariablesStack[StackIndex].empty())
        LiteralFn();
      else {
        const auto &Var = RandomVariable(StackIndex);
        if (Var.Type != Type)
          LiteralFn();
        else
          S << Var.Name;
      }
    };

    const std::string &T = F.ArgTypes[I];
    if (T == "int")
      EmitValue("int", [&S]() -> std::ostream & { return S << RandomNumber(); });
    else if (T == "float")
      EmitValue("float", [&S]() -> std::ostream & { return S << std::fixed << RandomFloat(); });
    else if (T == "bool")
      EmitValue("bool", [&S]() -> std::ostream & { return S << (RandomBool() ? "true" : "false"); });
    else if (T == "char")
       S << "'" << RandomLetter() << "'";

    if (I != Size - 1)
      S << ", ";
  }
  return S << ");";
}

std::ostream &RandomStmt(std::ostream &S) {
  switch (RandomNumber() % 22) {
  case 0: return RandomDoWhile(S);
  case 1: return RandomWhile(S);
  case 2: return RandomFor(S);
  case 3: return RandomIf(S);
  case 4: return RandomFunctionCall(S);
  default: return RandomVarDecl(S);
  }
}

std::ostream &RandomBlock(std::ostream &S) {
  VariablesStack.push_back({});
  S << "{\n";
  for (signed I = 5, Size = (RandomNumber() % 25) + I; I < Size; ++I)
    RandomVarDecl(S);
  for (signed I = 5, Size = (RandomNumber() % 10) + I; I < Size; ++I) {
    RandomStmt(S);
    S << '\n';
  }
  VariablesStack.pop_back();
  return S << "}\n";
}

std::ostream &RandomFunctionDecl(std::ostream &S) {
  VariablesStack.push_back({});

  std::string DataType = RandomDataType();
  std::string Name = RandomString();
  std::vector<std::string> ArgTypes;
  S << DataType << " " << Name;
  S << "(";
  for (signed I = 10, Size = (RandomNumber() % 10) + I; I < Size; ++I) {
    RandomVarDeclWithoutInitializer(S);
    ArgTypes.push_back(VariablesStack.back().back().Type);
    if (I != Size - 1)
      S << ", ";
  }
  S << ")\n{";

  for (signed I = 0; I < 10; ++I) {
    RandomStmt(S);
    S << '\n';
  }

  S << "return ";
  if (DataType == "int")
    S << RandomNumber();
  else if (DataType == "float")
    S << std::fixed << RandomFloat();
  else if (DataType == "char")
    S << "'" << RandomLetter() << "'";
  else if (DataType == "bool")
    S << (RandomBool() ? "true" : "false");
  S << ';';

  VariablesStack.pop_back();
  FunctionsStack.emplace_back(FunctionRecord{std::move(DataType), std::move(Name), std::move(ArgTypes)});
  return S << "\n}\n";
}

std::string GenerateFuzzProgram() {
  std::ostringstream Stream;
  for (signed I = 0; I < 10; ++I)
    RandomFunctionDecl(Stream);
  Stream << "\nint main() { return 0; }";
  VariablesStack.clear();
  FunctionsStack.clear();
  return Stream.str();
}

void PrintProgramWithLineNumbers(std::string_view Program) {
  size_t Pos = 0U;
  size_t LineNo = 0U;
  while (Pos != std::string_view::npos) {
    Pos = Program.find_first_of('\n');
    if (Pos == std::string_view::npos)
      break;
    std::string_view Line = Program.substr(0, Pos);
    std::cout << std::setw(6) << std::right << LineNo++ << ": ";
    std::cout << Line << '\n';
    std::cout << std::flush;
    Program = Program.substr(Pos + 1);
  }
}

int main() {
  for (signed I = 0; ; ++I) {
    std::cout << "#" << std::setw(5) << I << " fuzz test... "  << std::flush;
    std::string Program = GenerateFuzzProgram();
    std::ofstream TmpFile("/tmp/last.wl", std::ios::out);
    TmpFile << Program;
    TmpFile.close();
    try {
      weak::Lexer Lex(&Program.front(), &Program.back());
      auto Tokens = Lex.Analyze();
      weak::Parser Parser(&Tokens.front(), &Tokens.back());
      auto AST = Parser.Parse();
      std::vector<weak::Analysis *> Analyzers;
      Analyzers.push_back(new weak::VariableUseAnalysis(AST.get()));
      Analyzers.push_back(new weak::FunctionAnalysis(AST.get()));
      Analyzers.push_back(new weak::TypeAnalysis(AST.get()));

      for (auto *A : Analyzers) {
        A->Analyze();
        delete A;
      }
      weak::CodeGen CG(AST.get());
      CG.CreateCode();
      weak::RunBuiltinLLVMOptimizationPass(CG.Module(), O0);
      weak::Driver Driver(CG.Module(), "/tmp/code.wl");
      Driver.Compile();
    } catch (std::exception &E) {
      std::cout << "For program\n";
      PrintProgramWithLineNumbers(Program);
      std::cout << "\nCaught error: " << E.what() << std::endl;
      return -1;
    }

    std::cout << " success!\n" << std::flush;
  }
}