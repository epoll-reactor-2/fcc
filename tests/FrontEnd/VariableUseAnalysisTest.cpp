#include "FrontEnd/Lex/Lexer.h"
#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "Utility/Diagnostic.h"
#include <fstream>
#include <sstream>
#include <iostream>
#include <filesystem>

std::string ExtractExpectedWarns(std::string Program) {
  if (Program.substr(0, 3) != "// ") {
    std::cerr << "Expected warnings.";
    exit(-1);
  }

  std::string Warns;

  using namespace std::string_view_literals;
  while (Program.size() > 3 && Program.substr(0, 3) == "// ") {
    const auto EOL = Program.find_first_of('\n');
    std::string Line = Program.substr(3, EOL - "// "sv.length());
    Program = Program.substr(EOL + 1);
    Warns += Line;
    Warns += '\n';
  }

  return Warns;
}

std::vector<weak::Token> DoLexicalAnalysis(std::string_view Program, std::ostream &WarnStream) {
  weak::Lexer Lex(&*Program.begin(), &*Program.end());
  weak::PrintGeneratedWarns(WarnStream);
  return Lex.Analyze();
}

void TestAnalysis(std::string_view Path) {
  std::cout << "Testing file " << Path << "... ";

  std::ifstream File(Path.data());
  std::string Program((std::istreambuf_iterator<char>(File)),
                      (std::istreambuf_iterator<char>()));

  std::ostringstream WarnStream;

  auto Tokens = DoLexicalAnalysis(Program, WarnStream);
  weak::Parser Parser(&*Tokens.begin(), &*Tokens.end());
  auto AST = Parser.Parse();

  /// \todo: Compiler options.
  std::vector<weak::Analysis *> Analyzers;
  Analyzers.push_back(new weak::VariableUseAnalysis(AST.get()));

  for (auto *A : Analyzers) {
    A->Analyze();
    delete A;
  }

  weak::PrintGeneratedWarns(WarnStream);

  std::string GeneratedWarns = WarnStream.str();
  std::string ExpectedWarns = ExtractExpectedWarns(Program);

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

int main() {
  auto Dir = std::filesystem::directory_iterator(
    std::filesystem::current_path().concat("/VariableUseAnalysis"));
  for (const auto &File : Dir) {
    const auto &Path = File.path();
    if (Path.extension() == ".wl")
      TestAnalysis(Path.native());
  }
}
