/* Lexer.cpp - Implementation of lexical analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Lex/Lexer.h"
#include "Utility/Diagnostic.h"
#include <cassert>
#include <unordered_map>

auto &operator+=(std::vector<weak::Token> &V, weak::Token T) {
  V.push_back(std::move(T));
  return V;
}

namespace weak {
namespace {
static const std::unordered_map<std::string_view, TokenType> LexKeywords = {
    {"bool", TOK_BOOL},     {"break", TOK_BREAK},
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
    {".", TOK_DOT},
    {",", TOK_COMMA},
    {";", TOK_SEMICOLON},
    {"!", TOK_NOT},
    {"[", TOK_OPEN_BOX_BRACKET},
    {"]", TOK_CLOSE_BOX_BRACKET},
    {"{", TOK_OPEN_CURLY_BRACKET},
    {"}", TOK_CLOSE_CURLY_BRACKET},
    {"(", TOK_OPEN_PAREN},
    {")", TOK_CLOSE_PAREN}};

} // namespace

static void NormalizeColumnPos(std::string_view Data, weak::TokenType Type,
                               unsigned &ColumnNo) {
  using namespace std::string_view_literals;

  static const std::unordered_map TokenLengths{
      std::make_pair(TOK_BOOL, "bool"sv.length()),
      {TOK_BREAK, "break"sv.length()},
      {TOK_CHAR, "char"sv.length()},
      {TOK_CONTINUE, "continue"sv.length()},
      {TOK_DO, "do"sv.length()},
      {TOK_ELSE, "else"sv.length()},
      {TOK_FALSE, "false"sv.length()},
      {TOK_FLOAT, "float"sv.length()},
      {TOK_FOR, "for"sv.length()},
      {TOK_IF, "if"sv.length()},
      {TOK_INT, "int"sv.length()},
      {TOK_RETURN, "return"sv.length()},
      {TOK_STRING, "string"sv.length()},
      {TOK_TRUE, "true"sv.length()},
      {TOK_VOID, "void"sv.length()},
      {TOK_WHILE, "while"sv.length()}};

  if (auto It = TokenLengths.find(Type); It != TokenLengths.end()) {
    ColumnNo -= It->second;
    return;
  }

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

Lexer::Lexer(const char *TheBufStart, const char *TheBufEnd)
    : mBufStart(TheBufStart), mBufEnd(TheBufEnd), mBufPtr(TheBufStart),
      mLineNo(1U), mColumnNo(1U) {
  assert(mBufStart);
  assert(mBufEnd);
  assert(mBufStart <= mBufEnd);
}

std::vector<Token> Lexer::Analyze() {
  std::vector<Token> Tokens;

  Tokens.reserve(std::distance(mBufStart, mBufEnd) / 2);

  while (mBufPtr != mBufEnd)
    if (char C = PeekCurrent(); std::isdigit(C))
      Tokens += AnalyzeDigit();
    else if (std::isalpha(C))
      Tokens += AnalyzeSymbol();
    else if (C == '\'')
      Tokens += AnalyzeCharLiteral();
    else if (C == '\"')
      Tokens += AnalyzeStringLiteral();
    else if (C == '/')
      if (char Next = *(mBufPtr + 1); Next == '/' || Next == '*')
        ProcessComment();
      else
        /// Special case for '/='.
        Tokens += AnalyzeOperator();
    else if (std::isspace(C))
      PeekNext();
    else
      Tokens += AnalyzeOperator();

  return Tokens;
}

Token Lexer::AnalyzeDigit() {
  std::string Digit;
  bool DotError = false;
  unsigned DotErrorColumnNo = 1U;
  unsigned DotsReached = 0U;

  for (char C = PeekCurrent(); std::isdigit(C) || C == '.';) {
    if (C == '.')
      ++DotsReached;

    if (DotsReached > 1) {
      DotError = true;
      DotErrorColumnNo = mColumnNo;
      break;
    }

    Digit += PeekNext();
    C = PeekCurrent();
  }

  unsigned ColNo = DotError ? DotErrorColumnNo : mColumnNo;

  if (DotsReached > 1)
    weak::CompileError(mLineNo, ColNo) << "Extra \".\" in digit";

  if (std::isalpha(PeekCurrent()) || !std::isdigit(Digit.back()))
    weak::CompileError(mLineNo, ColNo) << "Digit as last character expected";

  return MakeToken(std::move(Digit), DotsReached == 0U
                                         ? TOK_INTEGRAL_LITERAL
                                         : TOK_FLOATING_POINT_LITERAL);
}

Token Lexer::AnalyzeCharLiteral() {
  Require('\'');
  char C = PeekNext();
  Require('\'');
  return MakeToken(std::string{C}, TOK_CHAR_LITERAL);
}

Token Lexer::AnalyzeStringLiteral() {
  Require('"');

  if (PeekNext() == '\"')
    return MakeToken("", TOK_STRING_LITERAL);

  --mBufPtr;

  std::string Literal;
  while (PeekCurrent() != '\"') {
    Literal += PeekNext();

    if (char C = PeekCurrent(); C == '\n' || C == '\0')
      weak::CompileError(mLineNo, mColumnNo)
          << "Closing \" expected, got `" << C << "`";

    if (Literal.back() == '\\')
      Literal.back() = PeekNext();
  }

  Require('"');
  --mColumnNo;

  return MakeToken(std::move(Literal), TOK_STRING_LITERAL);
}

Token Lexer::AnalyzeSymbol() {
  std::string Symbol;

  char C = PeekCurrent();
  while (isalpha(C) || C == '_' || isdigit(C)) {
    Symbol += PeekNext();
    C = PeekCurrent();
  }

  if (LexKeywords.find(Symbol) != LexKeywords.end())
    return MakeToken("", LexKeywords.at(Symbol));

  return MakeToken(std::move(Symbol), TOK_SYMBOL);
}

Token Lexer::AnalyzeOperator() {
  std::string Operator{PeekNext()};
  unsigned SavedColumnNo = 1U;
  char WrongOperator = '\0';

  /// This is actually implementation of maximal munch algorithm.
  /// We start to find from shortest to longest operator, for example,
  /// first `+`, next we ask hashmap if it contains `++` operator.
  /// If so, update result.
  ///
  /// This approach requires direct "road" from the shortest to the
  /// longest operator. It means, we cannot parse '>>=' operator, if we
  /// have no '>' and '>>' operators.
  while (true) {
    if (LexOperators.find(Operator) == LexOperators.end()) {
      WrongOperator = Operator.front();
      Operator.pop_back();
      --mBufPtr;

      if (mColumnNo > 1U)
        --mColumnNo;

      if (PeekCurrent() == '\n')
        --mLineNo;

      break;
    }

    char Next = *mBufPtr++;
    SavedColumnNo = mColumnNo;
    if (Next == '\n') {
      mColumnNo = 1U;
      ++mLineNo;
    }
    ++mColumnNo;
    Operator += Next;
  }

  if (!Operator.empty())
    return Token("", LexOperators.at(Operator), mLineNo,
                 SavedColumnNo - Operator.length());

  weak::CompileError(mLineNo, mColumnNo)
      << "Unknown character `" << WrongOperator << "`";
  Unreachable();
}

void Lexer::ProcessComment() {
  PeekNext();
  char C = PeekCurrent();

  if (C == '/')
    return ProcessOneLineComment();

  if (C == '*')
    return ProcessMultiLineComment();
}

void Lexer::ProcessOneLineComment() {
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

void Lexer::Require(char Expected) {
  if (char C = PeekNext(); C != Expected)
    weak::CompileError(mLineNo, mColumnNo)
        << "Expected `" << Expected << "`, got `" << C << "`";
}

char Lexer::PeekNext() {
  char Atom = *mBufPtr++;

  if (Atom == '\n')
    mLineNo++, mColumnNo = 1U;
  else
    mColumnNo++;

  return Atom;
}

char Lexer::PeekCurrent() const { return *mBufPtr; }

Token Lexer::MakeToken(std::string Data, TokenType Type) const {
  unsigned CurrLineNo = mLineNo;
  unsigned CurrColumnNo = mColumnNo;

  NormalizeColumnPos(Data, Type, CurrColumnNo);
  return Token(std::move(Data), Type, CurrLineNo, CurrColumnNo);
}

} // namespace weak