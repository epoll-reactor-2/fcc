#include "FrontEnd/Parse/Parser.hpp"
#include "FrontEnd/AST/ASTDump.hpp"
#include "FrontEnd/Lex/Lexer.hpp"
#include <filesystem>
#include <fstream>
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
  ExpectedAST.reserve(4096);

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
  std::ifstream File(Path.data());
  std::string Program((std::istreambuf_iterator<char>(File)),
                      (std::istreambuf_iterator<char>()));
  weak::Lexer Lex(&*Program.begin(), &*Program.end());
  auto Tokens = Lex.Analyze();
  weak::Parser Parser(&*Tokens.begin(), &*Tokens.end());
  auto AST = Parser.Parse();

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