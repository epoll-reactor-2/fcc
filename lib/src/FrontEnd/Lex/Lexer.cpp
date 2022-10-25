/* Lexer.cpp - Implementation of lexical analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Lex/Lexer.hpp"
#include "Utility/Diagnostic.hpp"
#include <algorithm>
#include <array>
#include <cassert>
#include <unordered_map>

namespace weak {
namespace {
static const std::unordered_map<std::string_view, TokenType> LexKeywords = {
    {"bool", TOK_BOOLEAN},  {"break", TOK_BREAK},
    {"char", TOK_CHAR},     {"continue", TOK_CONTINUE},
    {"do", TOK_DO},         {"else", TOK_ELSE},
    {"false", TOK_FALSE},   {"float", TOK_FLOAT},
    {"for", TOK_FOR},       {"if", TOK_IF},
    {"int", TOK_INT},       {"return", TOK_RETURN},
    {"string", TOK_STRING}, {"struct", TOK_STRUCT},
    {"true", TOK_TRUE},     {"void", TOK_VOID},
    {"while", TOK_WHILE}};

static const std::unordered_map<std::string_view, TokenType> LexOperators = {
    {"=", TOK_ASSIGN},
    {"*=", TOK_MUL_ASSIGN},
    {"/=", TOK_DIV_ASSIGN},
    {"%=", TOK_MOD_ASSIGN},
    {"+=", TOK_PLUS_ASSIGN},
    {"-=", TOK_MINUS_ASSIGN},
    {"<<=", TOK_SHL_ASSIGN},
    {">>=", TOK_SHR_ASSIGN},
    {"&=", TOK_BIT_AND_ASSIGN},
    {"|=", TOK_BIT_OR_ASSIGN},
    {"^=", TOK_XOR_ASSIGN},
    {"&&", TOK_AND},
    {"||", TOK_OR},
    {"^", TOK_XOR},
    {"&", TOK_BIT_AND},
    {"|", TOK_BIT_OR},
    {"==", TOK_EQ},
    {"!=", TOK_NEQ},
    {">", TOK_GT},
    {"<", TOK_LT},
    {">=", TOK_GE},
    {"<=", TOK_LE},
    {">>", TOK_SHR},
    {"<<", TOK_SHL},
    {"+", TOK_PLUS},
    {"-", TOK_MINUS},
    {"*", TOK_STAR},
    {"/", TOK_SLASH},
    {"%", TOK_MOD},
    {"++", TOK_INC},
    {"--", TOK_DEC},
    {",", TOK_COMMA},
    {";", TOK_SEMICOLON},
    {"!", TOK_NOT},
    {"[", TOK_OPEN_BOX_BRACKET},
    {"]", TOK_CLOSE_BOX_BRACKET},
    {"{", TOK_OPEN_CURLY_BRACKET},
    {"}", TOK_CLOSE_CURLY_BRACKET},
    {"(", TOK_OPEN_PAREN},
    {")", TOK_CLOSE_PAREN}};

class LexStringLiteralCheck {
public:
  explicit LexStringLiteralCheck(char ThePeek) : Peek(ThePeek) {}

  void ClosingQuoteCheck(unsigned LineNo, unsigned ColumnNo) const {
    if (Peek == '\n' || Peek == '\0')
      weak::CompileError(LineNo, ColumnNo) << "Closing \" expected";
  }

private:
  char Peek;
};

class LexDigitCheck {
public:
  LexDigitCheck(const std::string &TheDigit, char ThePeek, unsigned Dots)
      : Digit(TheDigit), Peek(ThePeek), DotsReached(Dots) {}

  void LastDigitRequire(unsigned LineNo, unsigned ColumnNo) const {
    if (std::isalpha(Peek) || !std::isdigit(Digit.back()))
      weak::CompileError(LineNo, ColumnNo)
          << "Digit as last character expected";
  }

  void ExactOneDotRequire(unsigned LineNo, unsigned ColumnNo) const {
    if (DotsReached > 1)
      weak::CompileError(LineNo, ColumnNo) << "Extra \".\" in digit";
  }

private:
  const std::string &Digit;
  char Peek;
  unsigned DotsReached;
};

} // namespace

static bool IsAlphanumeric(char C) { return isalpha(C) || C == '_'; }

static void NormalizeColumnPosition(std::string_view Data, weak::TokenType Type,
                                    unsigned &ColumnNo) {
  using namespace std::string_view_literals;
  static constexpr std::array TokenLengths{
      std::make_pair(TOK_BOOLEAN, "bool"sv.length()),
      std::make_pair(TOK_BREAK, "break"sv.length()),
      std::make_pair(TOK_CHAR, "char"sv.length()),
      std::make_pair(TOK_CONTINUE, "continue"sv.length()),
      std::make_pair(TOK_DO, "do"sv.length()),
      std::make_pair(TOK_ELSE, "else"sv.length()),
      std::make_pair(TOK_FALSE, "false"sv.length()),
      std::make_pair(TOK_FLOAT, "float"sv.length()),
      std::make_pair(TOK_FOR, "for"sv.length()),
      std::make_pair(TOK_IF, "if"sv.length()),
      std::make_pair(TOK_INT, "int"sv.length()),
      std::make_pair(TOK_RETURN, "return"sv.length()),
      std::make_pair(TOK_STRING, "string"sv.length()),
      std::make_pair(TOK_TRUE, "true"sv.length()),
      std::make_pair(TOK_VOID, "void"sv.length()),
      std::make_pair(TOK_WHILE, "while"sv.length())};

  if (const auto *It =
          std::find_if(TokenLengths.begin(), TokenLengths.end(),
                       [&](const auto &Pair) { return Type == Pair.first; });
      It != TokenLengths.end()) {
    ColumnNo -= It->second;
  } else {
    switch (Type) {
    case TOK_INTEGRAL_LITERAL:
    case TOK_FLOATING_POINT_LITERAL:
    case TOK_SYMBOL:
      ColumnNo -= Data.length();
      break;
    case TOK_STRING_LITERAL:
      ColumnNo -= (Data.length() + 2 /* Quotes. */);
      break;
    default:
      break;
    }
  }
}

Lexer::Lexer(const char *TheBufferStart, const char *TheBufferEnd)
    : BufferStart(TheBufferStart), BufferEnd(TheBufferEnd),
      CurrentBufferPtr(TheBufferStart), CurrentLineNo(1U), CurrentColumnNo(1U) {
  assert(BufferStart);
  assert(BufferEnd);
  assert(BufferStart <= BufferEnd);
}

const std::vector<Token> &Lexer::Analyze() {
  ProcessedTokens.clear();

  long InputSize = std::distance(BufferStart, BufferEnd);
  ProcessedTokens.reserve(InputSize / 2);

  while (CurrentBufferPtr != BufferEnd) {
    if (char Atom = PeekCurrent(); std::isdigit(Atom)) {
      ProcessedTokens.push_back(AnalyzeDigit());
    } else if (std::isalpha(Atom)) {
      ProcessedTokens.push_back(AnalyzeSymbol());
    } else if (Atom == '\'') {
      ProcessedTokens.push_back(AnalyzeCharLiteral());
    } else if (Atom == '\"') {
      ProcessedTokens.push_back(AnalyzeStringLiteral());
    } else if (Atom == '/') {
      ProcessComment();
    } else if (std::isspace(Atom)) {
      PeekNext();
      continue;
    } else {
      ProcessedTokens.push_back(AnalyzeOperator());
    }
  }

  return ProcessedTokens;
}

Token Lexer::AnalyzeDigit() {
  std::string Digit;
  bool DotErrorOccurred = false;
  unsigned DotErrorColumn = 1U;
  unsigned DotsReached = 0U;

  while (std::isdigit(PeekCurrent()) || PeekCurrent() == '.') {
    if (PeekCurrent() == '.')
      ++DotsReached;

    if (DotsReached > 1) {
      DotErrorOccurred = true;
      DotErrorColumn = CurrentColumnNo;
      break;
    }

    Digit += PeekNext();
  }

  unsigned LexColumnName = DotErrorOccurred ? DotErrorColumn : CurrentColumnNo;

  LexDigitCheck Checker(Digit, PeekCurrent(), DotsReached);
  Checker.LastDigitRequire(CurrentLineNo, LexColumnName);
  Checker.ExactOneDotRequire(CurrentLineNo, LexColumnName);

  return MakeToken(Digit, DotsReached == 0U ? TOK_INTEGRAL_LITERAL
                                            : TOK_FLOATING_POINT_LITERAL);
}

Token Lexer::AnalyzeCharLiteral() {
  PeekNext(); // Eat '
  char Character = PeekNext();
  PeekNext(); // Eat '
  return MakeToken(std::string{Character}, TOK_CHAR_LITERAL);
}

Token Lexer::AnalyzeStringLiteral() {
  PeekNext(); // Eat "

  if (PeekNext() == '\"')
    return MakeToken("", TOK_STRING_LITERAL);

  --CurrentBufferPtr;

  std::string Literal;
  while (PeekCurrent() != '\"') {
    Literal += PeekNext();

    LexStringLiteralCheck Check(PeekCurrent());
    Check.ClosingQuoteCheck(CurrentLineNo, CurrentColumnNo);

    if (Literal.back() == '\\')
      Literal.back() = PeekNext();
  }
  assert(PeekCurrent() == '\"');

  PeekNext(); // Eat "
  --CurrentColumnNo;

  return MakeToken(Literal, TOK_STRING_LITERAL);
}

Token Lexer::AnalyzeSymbol() {
  std::string Symbol;

  while ((IsAlphanumeric(PeekCurrent()) || std::isdigit(PeekCurrent())))
    Symbol += PeekNext();

  if (LexKeywords.find(Symbol) != LexKeywords.end())
    return MakeToken("", LexKeywords.at(Symbol));

  unsigned LineNo = CurrentLineNo;
  unsigned ColumnNo = CurrentColumnNo;

  NormalizeColumnPosition(Symbol, TOK_SYMBOL, ColumnNo);

  return Token(std::move(Symbol), TOK_SYMBOL, LineNo, ColumnNo);
}

Token Lexer::AnalyzeOperator() {
  std::string Operator{PeekNext()};
  unsigned SavedColumnNo = 1U;
  bool SearchFailed = false;
  char WrongOperator = '\0';

  while (true) {
    if (LexOperators.find(Operator) == LexOperators.end()) {
      WrongOperator = Operator.front();
      Operator.pop_back();
      --CurrentBufferPtr;

      if (CurrentColumnNo > 1U)
        --CurrentColumnNo;

      if (PeekCurrent() == '\n')
        --CurrentLineNo;

      SearchFailed = true;
      break;
    }

    char Next = *CurrentBufferPtr++;
    SavedColumnNo = CurrentColumnNo;
    if (Next == '\n') {
      CurrentColumnNo = 1U;
      CurrentLineNo++;
    }
    ++CurrentColumnNo;
    Operator += Next;
  }

  if (SearchFailed && !Operator.empty()) {
    return Token("", LexOperators.at(Operator), CurrentLineNo,
                 SavedColumnNo - Operator.length());
  }

  --CurrentColumnNo;
  weak::CompileError(CurrentLineNo, CurrentColumnNo)
      << "Unknown character sequence `" << WrongOperator << "`";
  weak::UnreachablePoint();
}

void Lexer::ProcessComment() {
  assert(PeekCurrent() == '/');
  PeekNext();
  char Atom = PeekCurrent();

  if (Atom == '/') {
    ProcessOneLineComment();
  } else if (Atom == '*') {
    ProcessMultiLineComment();
  } else {
    --CurrentBufferPtr;
    ProcessedTokens.push_back(AnalyzeOperator());
  }
}

void Lexer::ProcessOneLineComment() {
  PeekNext();

  while (PeekNext() != '\n')
    if (PeekCurrent() == '\n')
      break;
}

void Lexer::ProcessMultiLineComment() {
  PeekNext();

  while (true) {
    char Next = PeekCurrent();

    if (Next == '*') {
      PeekNext();
      Next = PeekCurrent();

      if (Next == '/') {
        PeekNext();
        break;
      }
    }

    PeekNext();
  }
}

char Lexer::PeekNext() {
  char Atom = *CurrentBufferPtr++;
  if (Atom == '\n') {
    CurrentLineNo++;
    CurrentColumnNo = 1U;
  } else {
    CurrentColumnNo++;
  }
  return Atom;
}

char Lexer::PeekCurrent() const { return *CurrentBufferPtr; }

Token Lexer::MakeToken(std::string Data, TokenType Type) const {
  unsigned LineNo = CurrentLineNo;
  unsigned ColumnNo = CurrentColumnNo;

  NormalizeColumnPosition(Data, Type, ColumnNo);
  return Token(std::move(Data), Type, LineNo, ColumnNo);
}

} // namespace weak