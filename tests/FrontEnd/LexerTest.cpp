#include "FrontEnd/Lex/Lexer.h"
#include "Utility/Diagnostic.h"
#include "TestHelpers.h"
#include <iostream>

weak::Token MakeToken(std::string Data, weak::TokenType Type) {
  return {std::move(Data), Type, 0U, 0U};
}

void RunLexerTest(std::string_view Input,
                         const std::vector<weak::Token> &ExpectedTokens) {
  auto Tokens = weak::Lexer(Input.begin(), Input.end()).Analyze();

  weak::PrintGeneratedWarns(std::cout);

  if (Tokens.size() != ExpectedTokens.size()) {
    std::cerr << "Output size mismatch: got " << Tokens.size()
              << " but expected " << ExpectedTokens.size();
    exit(-1);
  }
  for (size_t I = 0; I < Tokens.size(); ++I) {
    std::cout << "Token at line " << Tokens[I].LineNo << ", column "
              << Tokens[I].ColumnNo << ": " << TokenToString(Tokens[I].Type)
              << std::endl;
    if (Tokens[I] != ExpectedTokens[I]) {
      std::cerr << "got " << Tokens[I].Data << ", but expected "
                << ExpectedTokens[I].Data;
      exit(-1);
    }
  }
}

int main() {
  // This should not be correctly processed, since
  // there is no newline symbol at the end of comment.
  // SECTION(LexingEmptyOneLineComment) {
  //   std::vector<Token> Assertion = {};
  //   RunLexerTest("//", Assertion);
  // }
  using namespace weak;
  SECTION(LexingEmptyOneLineCommentExplicitlyTerminated) {
    std::vector<Token> Assertion = {};
    RunLexerTest("//\n", Assertion);
  }
  SECTION(LexingOneLineComment) {
    std::vector<Token> Assertion = {
        MakeToken("1", TOK_INTEGRAL_LITERAL),
        MakeToken("22", TOK_INTEGRAL_LITERAL),
        MakeToken("333", TOK_INTEGRAL_LITERAL),
        MakeToken("", TOK_SLASH)};
    RunLexerTest("// Free text.\n1 22 333 /", Assertion);
  }
  SECTION(LexingEmptyMultiLineComment) {
    std::vector<Token> Assertion = {};
    RunLexerTest("/**/", Assertion);
  }
  SECTION(LexingMultiLineComment) {
    std::vector<Token> Assertion = {
        MakeToken("1", TOK_INTEGRAL_LITERAL),
        MakeToken("22", TOK_INTEGRAL_LITERAL),
        MakeToken("333", TOK_INTEGRAL_LITERAL),
        MakeToken("", TOK_SLASH),
        MakeToken("", TOK_SLASH),
        MakeToken("", TOK_SLASH)};
    RunLexerTest("/* Free // text. */1 22 333 / / /", Assertion);
  }
  SECTION(LexingIntegralConstant) {
    std::vector<Token> Assertion = {
        MakeToken("1", TOK_INTEGRAL_LITERAL),
        MakeToken("22", TOK_INTEGRAL_LITERAL),
        MakeToken("333", TOK_INTEGRAL_LITERAL)};
    RunLexerTest("1 22 333", Assertion);
  }
  SECTION(LexingFloatingPointConstant) {
    std::vector<Token> Assertion = {
        MakeToken("1.1", TOK_FLOATING_POINT_LITERAL),
        MakeToken("22.22", TOK_FLOATING_POINT_LITERAL),
        MakeToken("333.333", TOK_FLOATING_POINT_LITERAL)};
    RunLexerTest("1.1 22.22 333.333", Assertion);
  }
  SECTION(LexingCharLiteralLiteral) {
    std::vector<Token> Assertion = {MakeToken("a", TOK_CHAR_LITERAL)};
    RunLexerTest("'a'", Assertion);
  }
  SECTION(LexingEmptyStringLiteral) {
    std::vector<Token> Assertion = {MakeToken("", TOK_STRING_LITERAL)};
    RunLexerTest("\"\"", Assertion);
  }
  SECTION(LexingStringLiteral) {
    std::vector<Token> Assertion = {MakeToken("a", TOK_STRING_LITERAL),
                                    MakeToken("b", TOK_STRING_LITERAL),
                                    MakeToken("c", TOK_STRING_LITERAL)};
    RunLexerTest(R"("a" "b" "c")", Assertion);
  }
  SECTION(LexingStringLiteral) {
    std::vector<Token> Assertion = {MakeToken("text \" with escaped character ",
                                              TOK_STRING_LITERAL)};
    RunLexerTest(R"("text \" with escaped character ")", Assertion);
  }
  SECTION(LexingEscapeSequenceInStringLiteral) {
    std::vector<Token> Assertion = {
        MakeToken("\\escaped\\", TOK_STRING_LITERAL)};
    RunLexerTest(R"("\\escaped\\")", Assertion);
  }
  SECTION(LexingSymbols) {
    std::vector<Token> Assertion = {MakeToken("a", TOK_SYMBOL),
                                    MakeToken("b", TOK_SYMBOL),
                                    MakeToken("c", TOK_SYMBOL)};
    RunLexerTest("a b c", Assertion);
  }
  SECTION(LexingKeywords) {
    std::vector<Token> Assertion = {MakeToken("", TOK_BOOL),
                                    MakeToken("", TOK_CHAR),
                                    MakeToken("", TOK_WHILE)};
    RunLexerTest("bool\nchar\nwhile", Assertion);
  }
  SECTION(LexingOperators) {
    std::vector<Token> Assertion_1 = {MakeToken("", TOK_PLUS),
                                      MakeToken("", TOK_MINUS),
                                      MakeToken("", TOK_SLASH)};
    RunLexerTest("+-/", Assertion_1);
    std::vector<Token> Assertion_2 = {
        MakeToken("", TOK_INC), MakeToken("", TOK_INC),
        MakeToken("", TOK_INC), MakeToken("", TOK_PLUS)};
    RunLexerTest("+++++++", Assertion_2);
  }
  SECTION(LexingCompoundInput) {
    std::vector<Token> Assertion = {
        MakeToken("", TOK_VOID),
        MakeToken("main", TOK_SYMBOL),
        MakeToken("", TOK_OPEN_PAREN),
        MakeToken("", TOK_INT),
        MakeToken("argc", TOK_SYMBOL),
        MakeToken("", TOK_COMMA),
        MakeToken("", TOK_CHAR),
        MakeToken("argv", TOK_SYMBOL),
        MakeToken("", TOK_CLOSE_PAREN),

        MakeToken("", TOK_OPEN_CURLY_BRACKET),
        MakeToken("", TOK_STRING),
        MakeToken("output", TOK_SYMBOL),
        MakeToken("", TOK_ASSIGN),
        MakeToken("", TOK_STRING_LITERAL),
        MakeToken("", TOK_SEMICOLON),

        MakeToken("", TOK_WHILE),
        MakeToken("", TOK_OPEN_PAREN),
        MakeToken("1", TOK_INTEGRAL_LITERAL),
        MakeToken("", TOK_NEQ),
        MakeToken("0", TOK_INTEGRAL_LITERAL),
        MakeToken("", TOK_CLOSE_PAREN),

        MakeToken("", TOK_OPEN_CURLY_BRACKET),

        MakeToken("output", TOK_SYMBOL),
        MakeToken("", TOK_PLUS_ASSIGN),
        MakeToken("Oder ist dieser Lastwagen vielleicht besser auf den blitzen "
                  "Zweiundzwanzigzöllner?",
                  TOK_STRING_LITERAL),
        MakeToken("", TOK_SEMICOLON),

        MakeToken("", TOK_CLOSE_CURLY_BRACKET),
        MakeToken("", TOK_CLOSE_CURLY_BRACKET)};
    RunLexerTest(R"__(void main(int argc, char argv) {
        string output = "";
        while (1 != 0) {
          output += "Oder ist dieser Lastwagen vielleicht besser auf den blitzen Zweiundzwanzigzöllner?";
        }
      }
    )__",
                 Assertion);
  }
  SECTION(LexerSpeedTest) {
    std::string Body =
        "1.1 1.1 1.1 1.1 1.1 1.1 1.1 1.1 1.1 1.1 1.1 1.1 1.1 1.1"
        "+++++++++++++++++++++++++++++++++++++++++++++++++++++++"
        "\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\""
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa ";
    for (size_t It = 0; It < 16; ++It)
      Body += std::string(Body);
    printf("Body size: %zu\n", Body.size());
    Lexer(&*Body.begin(), &*Body.end()).Analyze();
  }
}
