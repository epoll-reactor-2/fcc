#include "FrontEnd/Lex/Lexer.h"
#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/Analysis/FunctionAnalysis.h"
#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "Utility/Diagnostic.h"
#include "Utility/Files.h"
#include <iostream>
#include <filesystem>

std::string ExtractExpectedMsg(std::string_view Program) {
  if (Program.substr(0, 3) != "// ") {
    std::cerr << "Expected warnings.";
    exit(-1);
  }

  std::string Warns;

  using namespace std::string_view_literals;
  while (Program.size() > 3 && Program.substr(0, 3) == "// ") {
    const auto EOL = Program.find_first_of('\n');
    std::string_view Line = Program.substr(3, EOL - "// "sv.length());
    Program = Program.substr(EOL + 1);
    Warns += Line;
    Warns += '\n';
  }

  if (!Warns.empty())
    Warns.pop_back();

  return Warns;
}

std::vector<weak::Token> DoLexicalAnalysis(std::string_view Program, std::ostream &WarnStream) {
  weak::Lexer Lex(&*Program.begin(), &*Program.end());
  weak::PrintGeneratedWarns(WarnStream);
  return Lex.Analyze();
}

void AnalyzeWarns(std::string_view Program, std::ostringstream &WarnStream, weak::Analysis *Analysis) {
  Analysis->Analyze();

  weak::PrintGeneratedWarns(WarnStream);

  std::string GeneratedWarns = WarnStream.str();
  std::string ExpectedWarns = ExtractExpectedMsg(Program);

  if (GeneratedWarns == ExpectedWarns) {
    std::cout << "Success!" << std::endl;
    return;
  }

  std::cout << "Error while analyzing program:\n";
  std::cout << Program << '\n';
  std::cout << "Expected warnings are:\n";
  std::cout << ExpectedWarns;
  std::cout << "\ngenerated ones:\n";
  std::cout << GeneratedWarns;
  std::cout << "\n";
  exit(-1);
}

void AnalyzeErrors(std::string_view Program, weak::Analysis *Analysis) {
  try {
    Analysis->Analyze();
    std::cerr << "Program:\n";
    std::cerr << Program;
    std::cerr << "Expected error!\n";
    exit(-1);
  } catch (std::exception &E) {
    std::string ExpectedErrors = ExtractExpectedMsg(Program);
    std::string GeneratedErrors = E.what();

    if (GeneratedErrors == ExpectedErrors) {
      std::cout << "Success!" << std::endl;
      return;
    }

    std::cout << "Error while analyzing program:\n";
    std::cout << Program << '\n';
    std::cout << "Expected errors are:\n";
    std::cout << ExpectedErrors;
    std::cout << "\ngenerated ones:\n";
    std::cout << GeneratedErrors;
    std::cout << "\n";
    exit(-1);
  }
}

template <typename AnalysisForTest>
void TestAnalysis(std::string_view Path, bool IsWarnTest) {
  std::cout << "Testing file " << Path << "... ";

  std::string Program = weak::FileAsString(Path);

  std::ostringstream WarnStream;

  auto Tokens = DoLexicalAnalysis(Program, WarnStream);
  weak::Parser Parser(&*Tokens.begin(), &*Tokens.end());
  auto AST = Parser.Parse();

  /// \todo: Compiler options.
  auto *Analysis = new AnalysisForTest(AST.get());

  if (IsWarnTest)
    AnalyzeWarns(Program, WarnStream, Analysis);
  else
    AnalyzeErrors(Program, Analysis);

  delete Analysis;
}

template <typename Analysis>
void RunAnalysisTest(const char *TestsDir, bool IsWarnTest) {
  auto Dir = std::filesystem::directory_iterator(
    std::filesystem::current_path().concat(TestsDir));
  for (const auto& File: Dir) {
    const auto& Path = File.path();
    if (Path.extension() == ".wl")
      TestAnalysis<Analysis>(Path.native(), IsWarnTest);
  }
}

int main() {
  RunAnalysisTest<weak::FunctionAnalysis>("/FunctionAnalysis", /*IsWarnTest=*/false);
  RunAnalysisTest<weak::VariableUseAnalysis>("/VariableUseAnalysis/Warns", /*IsWarnTest=*/true);
  RunAnalysisTest<weak::VariableUseAnalysis>("/VariableUseAnalysis/Errors", /*IsWarnTest=*/false);
}