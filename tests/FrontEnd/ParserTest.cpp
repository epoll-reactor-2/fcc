#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/AST/ASTDump.h"
#include "FrontEnd/Lex/Lexer.h"
#include "Utility/Diagnostic.h"
#include "Utility/Files.h"
#include <filesystem>
#include <iostream>

/// This gets all contents of first comment placed
/// at the very beginning of input program.
/// F.e.
/// // This is
/// // extracted part,
/// // splitted into lines.
/// int main() { return 0; }
std::string ExtractAST(std::string Program) {
  std::string ExpectedAST;

  using namespace std::string_view_literals;
  while (Program.size() > 2 && Program.substr(0, 2) == "//") {
    const auto EOL = Program.find_first_of('\n');
    std::string Line = Program.substr(2, EOL - "//"sv.length());
    Program = Program.substr(EOL + 1);
    ExpectedAST += Line;
    ExpectedAST += '\n';
  }

  return ExpectedAST;
}

void TestAST(std::string_view Path) {
  std::cout << "Testing file " << Path << "...\n";
  std::string Program = weak::FileAsString(Path);

  weak::Lexer Lex(&Program.front(), &Program.back());
  auto Tokens = Lex.Analyze();
  weak::Parser Parser(&Tokens.front(), &Tokens.back());
  auto AST = Parser.Parse();

  weak::PrintGeneratedWarns(std::cout);

  std::ostringstream ASTStream;
  weak::ASTDump(AST.get(), ASTStream);

  std::string GeneratedAST = ASTStream.str();
  std::string ExpectedAST = ExtractAST(Program);

  if (ExpectedAST != GeneratedAST) {
    std::cout << "Error while analyzing program:\n";
    std::cout << Program << '\n';
    std::cout << "Expected AST:\n";
    std::cout << ExpectedAST;
    std::cout << "\nGenerated AST:\n";
    std::cout << GeneratedAST;
    std::cout << "\n";
    exit(-1);
  }
}

int main() {
  auto Dir = std::filesystem::directory_iterator(
      std::filesystem::current_path().concat("/Parser"));
  for (const auto &File : Dir) {
    const auto &Path = File.path();
    if (Path.extension() == ".wl")
      TestAST(Path.native());
  }
}