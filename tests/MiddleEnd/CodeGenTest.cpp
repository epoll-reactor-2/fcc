#include "FrontEnd/Lex/Lexer.hpp"
#include "FrontEnd/Parse/Parser.hpp"
#include "MiddleEnd/CodeGen/CodeGen.hpp"
#include "TestHelpers.hpp"
#include <fstream>
#include <filesystem>

namespace fe = weak::frontEnd;
namespace me = weak::middleEnd;

void RunFromFile(std::string_view Path) {
  llvm::errs() << "Testing file " << Path << "...\n";
  std::ifstream File(Path.data());
  std::string Program(
    (std::istreambuf_iterator<char>(File)),
    (std::istreambuf_iterator<char>()));
  fe::Lexer Lex(&*Program.begin(), &*Program.end());
  auto Tokens = Lex.Analyze();
  fe::Parser Parser(&*Tokens.begin(), &*Tokens.end());
  auto AST = Parser.Parse();
  me::CodeGen CodeGen(AST.get());

  std::string TargetPath(Path.substr(Path.find_last_of('/') + 1));
  TargetPath = TargetPath.substr(0, TargetPath.find_first_of('.'));

  using namespace std::string_view_literals;
  if (TargetPath.substr(0, "ExpectError"sv.size()) == "ExpectError") {
    try {
      CodeGen.CreateCode(TargetPath);
      llvm::errs() << "Expected error!";
      exit(-1);
    } catch (std::exception &Error) {
      llvm::errs() << "Catched expected error: " << Error.what() << '\n';
    }
  } else {
    CodeGen.CreateCode(TargetPath);
    llvm::errs() << CodeGen.ToString();
  }
}

int main() {
  auto Directory = std::filesystem::directory_iterator(
    std::filesystem::current_path());
  for (const auto &File : Directory) {
    if (File.path().extension() == ".wl") {
      RunFromFile(File.path().native());
    }
  }
}