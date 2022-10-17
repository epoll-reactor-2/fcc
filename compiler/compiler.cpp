#include "FrontEnd/AST/ASTDump.hpp"
#include "FrontEnd/Lex/Lexer.hpp"
#include "FrontEnd/Parse/Parser.hpp"
#include "MiddleEnd/CodeGen/CodeGen.hpp"
#include "MiddleEnd/CodeGen/TargetCodeBuilder.hpp"
#include "llvm/Support/CommandLine.h"
#include <fstream>
#include <iostream>
#include <iomanip>


std::vector<weak::Token> DoLexicalAnalysis(std::string_view InputPath) {
  std::ifstream File(InputPath.data());
  std::string Program(
      (std::istreambuf_iterator<char>(File)),
      (std::istreambuf_iterator<char>()));
  weak::Lexer Lex(&*Program.begin(), &*Program.end());
  auto Tokens = Lex.Analyze();
  return Tokens;
}

std::unique_ptr<weak::ASTNode> DoSyntaxAnalysis(std::string_view InputPath) {
  auto Tokens = DoLexicalAnalysis(InputPath);
  weak::Parser Parser(&*Tokens.begin(), &*Tokens.end());
  auto AST = Parser.Parse();
  return AST;
}

std::string DoLLVMCodeGen(std::string_view InputPath, std::string_view OutputPath) {
  auto AST = DoSyntaxAnalysis(InputPath);
  weak::CodeGen CodeGenerator(AST.get());
  CodeGenerator.CreateCode();
  return CodeGenerator.ToString();
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
  weak::ASTDump(AST, std::cout);
}

void DumpLLVMIR(std::string_view InputPath, std::string_view OutputPath) {
  std::string IR = DoLLVMCodeGen(InputPath, OutputPath);
  std::cout << IR << std::endl;
}

void BuildCode(std::string_view InputPath, std::string_view OutputPath) {
  auto AST = DoSyntaxAnalysis(InputPath);
  weak::CodeGen CodeGen(AST.get());
  CodeGen.CreateCode();
  weak::TargetCodeBuilder TargetCodeBuilder(CodeGen.GetModule(), OutputPath);
  TargetCodeBuilder.Build();
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

  llvm::cl::HideUnrelatedOptions(CompilerCategory);
  llvm::cl::ParseCommandLineOptions(Argc, Argv);

  std::string InputFilename = InputFilenameOpt;
  std::string OutputFilename = OutputFilenameOpt.empty()
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
    DumpLLVMIR(InputFilename, OutputFilename);
    return 0;
  }

  BuildCode(InputFilename, OutputFilename);
}