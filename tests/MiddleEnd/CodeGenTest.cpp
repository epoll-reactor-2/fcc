#include "MiddleEnd/CodeGen/CodeGen.h"
#include "FrontEnd/Lex/Lexer.h"
#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "FrontEnd/Analysis/FunctionAnalysis.h"
#include "FrontEnd/Analysis/TypeAnalysis.h"
#include "MiddleEnd/Driver/Driver.h"
#include "Utility/Diagnostic.h"
#include "Utility/Files.h"
#include <filesystem>
#include <iostream>

using namespace std::string_view_literals;

/// \note Codegen tests do not return values greater than 256 due to the
///       fact that process returns exit status modulo 256. By the way, this
///       works as well in C code.
int RunAndGetExitCode(const std::string &TargetPath) {
  int code = system(("./" + TargetPath).c_str());
  return WEXITSTATUS(code);
}

/// There semantic analysis expect to be correct.
void RunTestOnValidCode(
  std::vector<weak::Analysis *> &Analyzers,
  weak::CodeGen                 &CG,
  const std::string             &Program,
  const std::string             &PathToBin
);
/// There semantic or other analysis should emit error.
void RunTestOnInvalidCode(
  std::vector<weak::Analysis *> &Analyzers,
  weak::CodeGen                 &CG,
  const std::string             &Program
);

void RunTest(std::string_view Path, bool IsValid) {
  llvm::outs() << "Testing file " << Path << "... ";

  std::string Program = weak::FileAsString(Path);
  weak::Lexer Lex(&Program.front(), &Program.back());
  auto Tokens = Lex.Analyze();
  weak::Parser Parser(&Tokens.front(), &Tokens.back());
  auto AST = Parser.Parse();

  std::vector<weak::Analysis *> Analyzers;
  Analyzers.push_back(new weak::VariableUseAnalysis(AST.get()));
  Analyzers.push_back(new weak::FunctionAnalysis(AST.get()));
  Analyzers.push_back(new weak::TypeAnalysis(AST.get()));

  weak::CodeGen CG(AST.get());

  std::string PathToBin(Path.substr(Path.find_last_of('/') + 1));
  PathToBin = PathToBin.substr(0, PathToBin.find_first_of('.'));

  if (IsValid)
    RunTestOnValidCode(Analyzers, CG, Program, PathToBin);
  else
    RunTestOnInvalidCode(Analyzers, CG, Program);

  weak::PrintGeneratedWarns(std::cout);

  for (auto *A : Analyzers)
    delete A;
}

void RunTestOnValidCode(
  std::vector<weak::Analysis *> &Analyzers,
  weak::CodeGen                 &CG,
  const std::string             &Program,
  const std::string             &PathToBin
) {
  for (auto *A : Analyzers)
    A->Analyze();

  if (Program.substr(0, 3) != "// ") {
    llvm::errs() << "Expected planned exit code.";
    exit(-1);
  }
  int ExpectedExitCode = std::stoi(
    Program.substr(
      "// "sv.length(),
      Program.find_first_of('\n') - "// "sv.length()
    )
  );

  CG.CreateCode();
  weak::Driver Driver(CG.Module(), PathToBin);
  Driver.Compile();

  int ExitCode = RunAndGetExitCode(PathToBin);
  if (ExitCode != ExpectedExitCode) {
    llvm::errs()
      << "Process exited with wrong exit code: " << ExitCode
      << " got, but " << ExpectedExitCode << " expected.";
    exit(-1);
  } else
    llvm::outs() << "Success!\n";
}

void RunTestOnInvalidCode(
  std::vector<weak::Analysis *> &Analyzers,
  weak::CodeGen                 &CG,
  const std::string             &Program
) {
  if (Program.substr(0, 3) != "// ") {
    llvm::errs() << "Expected comment with error message.";
    exit(-1);
  }

  std::string ExpectedErrorMsg = Program.substr(
    "// "sv.length(),
    Program.find_first_of('\n') - "// "sv.length()
  );

  try {
    for (auto *A : Analyzers)
      A->Analyze();
    CG.CreateCode();
    llvm::errs() << "Expected error";
    exit(-1);
  } catch (std::exception &Error) {
    if (std::string(Error.what()) != ExpectedErrorMsg) {
      llvm::errs()
        << "Errors mismatch:\n\t" << Error.what()
        << "\ngot, but\n\t" << ExpectedErrorMsg << "\nexpected.";
      exit(-1);
    }
    llvm::outs() << "Caught expected error: " << Error.what() << '\n';
  }
}

int main() {
  auto Dir = std::filesystem::directory_iterator(
    std::filesystem::current_path().concat("/CodeGen/Valid")
  );
  for (const auto &File : Dir) {
    const auto &Path = File.path();
    if (Path.extension() == ".wl")
      RunTest(Path.native(), /*ValidFlag=*/true);
  }

  llvm::outs() << "All tests passed!";
}