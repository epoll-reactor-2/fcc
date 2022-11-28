#include "FrontEnd/AST/ASTDump.h"
#include "FrontEnd/Lex/Lexer.h"
#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/Analysis/FunctionAnalysis.h"
#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "FrontEnd/Analysis/TypeAnalysis.h"
#include "MiddleEnd/CodeGen/CodeGen.h"
#include "MiddleEnd/Driver/Driver.h"
#include "MiddleEnd/Optimizers/Optimizers.h"
#include "Utility/Diagnostic.h"
#include "Utility/Files.h"
#include "llvm/Support/CommandLine.h"
#include <iomanip>
#include <iostream>

std::vector<weak::Token> DoLexicalAnalysis(std::string_view Path) {
  std::string Program = weak::FileAsString(Path);
  weak::Lexer Lex(&Program.front(), &Program.back());
  weak::PrintGeneratedWarns(std::cout);
  return Lex.Analyze();
}

std::unique_ptr<weak::ASTCompound>
DoSyntaxAnalysis(std::string_view InputPath) {
  auto Tokens = DoLexicalAnalysis(InputPath);
  weak::Parser Parser(&Tokens.front(), &Tokens.back());
  auto AST = Parser.Parse();

  /// \todo: Compiler options.
  std::vector<weak::Analysis *> Analyzers;
  Analyzers.push_back(new weak::VariableUseAnalysis(AST.get()));
  Analyzers.push_back(new weak::FunctionAnalysis(AST.get()));
  Analyzers.push_back(new weak::TypeAnalysis(AST.get()));

  for (auto *A : Analyzers) {
    A->Analyze();
    delete A;
  }

  weak::PrintGeneratedWarns(std::cout);

  return AST;
}

std::string DoLLVMCodeGen(std::string_view InputPath, WeakOptimizationLevel OptLvl) {
  auto AST = DoSyntaxAnalysis(InputPath);
  weak::CodeGen CG(AST.get());
  CG.CreateCode();
  weak::RunBuiltinLLVMOptimizationPass(CG.Module(), OptLvl);
  weak::PrintGeneratedWarns(std::cout);
  return CG.ToString();
}

void DumpLexemes(std::string_view InputPath) {
  auto Tokens = DoLexicalAnalysis(InputPath);
  for (const weak::Token &T : Tokens) {
    std::cout << "Token " << std::setw(20) << weak::TokenToString(T.Type);
    std::cout << "  " << T.Data;
    std::cout << std::endl;
  }
}

void DumpAST(std::string_view InputPath) {
  auto AST = DoSyntaxAnalysis(InputPath);
  weak::ASTDump(AST.get(), std::cout);
}

void DumpLLVMIR(std::string_view InputPath, WeakOptimizationLevel OptLvl) {
  std::string IR = DoLLVMCodeGen(InputPath, OptLvl);
  std::cout << IR << std::endl;
}

void BuildCode(
  std::string_view      InputPath,
  std::string_view      OutputPath,
  WeakOptimizationLevel OptLvl
) {
  auto AST = DoSyntaxAnalysis(InputPath);
  weak::CodeGen CG(AST.get());
  CG.CreateCode();
  weak::RunBuiltinLLVMOptimizationPass(CG.Module(), OptLvl);
  weak::Driver Driver(CG.Module(), OutputPath);
  weak::PrintGeneratedWarns(std::cout);
  Driver.Compile();
}

int main(int Argc, char *Argv[]) {
  llvm::cl::OptionCategory
    CompilerCategory(
      "Compiler Options",
      "Options for controlling the compilation process.");

  llvm::cl::opt<std::string>
    InputFilenameOpt(
      "i",
      llvm::cl::desc("Specify input program file"),
      llvm::cl::Required,
      llvm::cl::cat(CompilerCategory));

  llvm::cl::opt<std::string>
    OutputFilenameOpt(
      "o",
      llvm::cl::desc("Specify executable file path"),
      llvm::cl::Optional,
      llvm::cl::cat(CompilerCategory));

  llvm::cl::opt<bool>
    DumpLexemesOpt(
      "dump-lexemes",
      llvm::cl::desc("Do lexical analysis of input file"),
      llvm::cl::Optional,
      llvm::cl::cat(CompilerCategory));

  llvm::cl::opt<bool>
    DumpASTOpt(
      "dump-ast",
      llvm::cl::desc("Show Abstract Syntax Tree of input file"),
      llvm::cl::Optional,
      llvm::cl::cat(CompilerCategory));

  llvm::cl::opt<bool>
    DumpLLVMIROpt(
      "dump-llvm",
      llvm::cl::desc("Show the LLVM IR of input file"),
      llvm::cl::Optional,
      llvm::cl::cat(CompilerCategory));

  llvm::cl::opt<WeakOptimizationLevel>
    OptimizationLvlOpt(
      llvm::cl::desc("Optimization level, from -O0 to -O3"),
      llvm::cl::values(
        clEnumVal(O0, "No optimizations"),
        clEnumVal(O1, "Trivial"),
        clEnumVal(O2, "Default"),
        clEnumVal(O3, "Most aggressive")),
      llvm::cl::init(O0));

  llvm::cl::HideUnrelatedOptions(CompilerCategory);
  llvm::cl::ParseCommandLineOptions(Argc, Argv);

  std::string InputFilename = InputFilenameOpt;
  std::string OutputFilename =
    OutputFilenameOpt.empty()
      ? InputFilename.substr(0, InputFilename.find_first_of('.'))
      : OutputFilenameOpt;

  if (DumpLexemesOpt) {
    DumpLexemes(InputFilename);
    return 0;
  }

  if (DumpASTOpt) {
    DumpAST(InputFilename);
    return 0;
  }

  if (DumpLLVMIROpt) {
    DumpLLVMIR(InputFilename, OptimizationLvlOpt);
    return 0;
  }

  BuildCode(InputFilename, OutputFilename, OptimizationLvlOpt);
}