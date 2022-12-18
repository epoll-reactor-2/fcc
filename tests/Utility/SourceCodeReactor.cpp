/*

*/

#include <algorithm>
#include <iostream>
#include <fstream>
#include <random>
#include <set>
#include <vector>

static const char *Operators[] = {
  "+",
  "-",
  "<<",
  "%",
  "/",
  "*"
};

static const char *DataTypes[] = {
  "int",
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
std::uniform_int_distribution<> NumericDistribution(0, 674545);
std::uniform_int_distribution<> LetterDistribution(0, std::size(LettersSet) - 1);
std::uniform_int_distribution<> OperatorsDistribution(0, std::size(Operators) - 1);
std::uniform_int_distribution<> DataTypesDistribution(0, std::size(DataTypes) - 1);
std::uniform_int_distribution<> BooleanDistribution(0, 1);

struct VariableStackRecord {
  std::string Type, Name;
};

std::vector<std::vector<VariableStackRecord>> VariablesStack(1);

signed RandomNumber() {
  return NumericDistribution(RandomEngine);
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

const char *RandomOperator() {
  return Operators[OperatorsDistribution(RandomEngine)];
}

const VariableStackRecord &RandomVariable() {
  if (VariablesStack.empty())
    throw std::logic_error("Empty variables stack");
  std::uniform_int_distribution<> VariableDistribution(0, VariablesStack.size() - 1);
  auto &R = VariablesStack.back();
  if (R.empty())
    throw std::logic_error("Empty scope variables stack");
  std::uniform_int_distribution<> ScopeDistribution(0, R.size() - 1);
  return R[ScopeDistribution(RandomEngine)];
}

std::string RandomString() {
  std::string String(32, 0);
  std::generate_n(String.begin(), 32, RandomLetter);
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

std::ostream &RandomBinary(std::ostream &S) {
  if (VariablesStack.empty() || VariablesStack.back().empty())
    S << RandomNumber();
  else {
    const auto &Var = RandomVariable();
    if (Var.Type != "int")
      S << RandomNumber() << " ";
    else
      S << Var.Name << " ";
  }
  S << RandomOperator() << " ";

//  S << RandomNumber() << " " << RandomOperator() << " ";
  /// Increasing or decreasing `%` operand, we set
  /// average binary chain length.
  if (RandomNumber() % 15 == 0) {
    if (VariablesStack.empty() || VariablesStack.back().empty())
      return S << RandomNumber() << " ";
    const auto &Var = RandomVariable();
    if (Var.Type != "int")
      return S << RandomNumber() << " ";
    return S << Var.Name << " ";
  }
  else
    return RandomBinary(S);
}

std::ostream &RandomVarDeclWithoutInitializer(std::ostream &S) {
  std::string Name = RandomString();
  std::string DT = RandomDataType();
  return S << RandomDataType() << ' ' << Name;
  VariablesStack.back().emplace_back(VariableStackRecord{DT, Name});
}

std::ostream &RandomVarDecl(std::ostream &S) {
  std::string Name = RandomString();
  std::string DT = RandomDataType();

  if (DT == "int") {
    S << "int " << Name << " = ";
    RandomBinary(S);
    S << ';';
  } else if (DT == "char") {
    S << "char " << Name << " = '" << RandomLetter() << "';";
  } else if (DT == "bool") {
    S << "bool " << Name << " = " << (RandomBool() ? "true" : "false") << ";";
  }

  VariablesStack.back().emplace_back(VariableStackRecord{DT, Name});
  return S;
}

std::ostream &RandomBlock(std::ostream &S);

std::ostream &RandomWhile(std::ostream &S) {
  printf("While\n");
  for (signed I = 5, Size = (RandomNumber() % 25) + I; I < Size; ++I)
    RandomVarDecl(S);
  S << "while (";
  RandomBinary(S);
  S << ")\n";
  RandomBlock(S);
  return S;
}

std::ostream &RandomStmt(std::ostream &S) {
  if (RandomNumber() % 5 != 0)
    return RandomVarDecl(S);
  else
    return RandomWhile(S);
}

std::ostream &RandomBlock(std::ostream &S) {
  printf("Block\n");
  VariablesStack.push_back({});
  S << "{\n";
  for (signed I = 5, Size = (RandomNumber() % 10) + I; I < Size; ++I) {
    RandomStmt(S);
    S << '\n';
  }
  VariablesStack.pop_back();
  return S << "}\n";
}

std::ostream &RandomFunctionDecl(std::ostream &S) {
  std::string DataType = RandomDataType();
  S << DataType << " " << RandomString();
  S << "(";
  for (signed I = 3, Size = (RandomNumber() % 11) + I; I < Size; ++I) {
    RandomVarDeclWithoutInitializer(S);
    if (I != Size - 1)
      S << ", ";
  }
  S << ")\n{";

  for (signed I = 10, Size = 100; I < Size; ++I) {
    RandomStmt(S);
    S << '\n';
  }

  S << "return ";
  if (DataType == "int")
    S << RandomNumber();
  if (DataType == "char")
    S << "'" << RandomLetter() << "'";
  if (DataType == "bool")
    S << (RandomBool() ? "true" : "false");
  S << ';';

  return S << "\n}\n";
}

int main() {
  std::ofstream TmpFile("/tmp/code.wl");
  for (signed I = 0; I < 1; ++I) {
    RandomFunctionDecl(TmpFile);
    TmpFile << '\n';
  }

  TmpFile << "int main() { return 0; }";
}