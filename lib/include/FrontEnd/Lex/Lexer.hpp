/* Lexer.hpp - Implementation of lexical analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_LEXER_HPP
#define WEAK_COMPILER_FRONTEND_LEX_LEXER_HPP

#include "FrontEnd/Lex/Token.hpp"
#include <vector>

namespace weak {

/// \brief Lexical analyzer.
///
/// Provides interface to transform plain text
/// into a stream of tokens.
class Lexer {
public:
  Lexer(const char *TheBufStart, const char *TheBufEnd);

  /// Walk through input text and generate stream of tokens.
  std::vector<Token> Analyze();

private:
  Token AnalyzeDigit();
  Token AnalyzeCharLiteral();
  Token AnalyzeStringLiteral();
  Token AnalyzeSymbol();
  Token AnalyzeOperator();

  /// Ignore C-style one-line and multi-line comments.
  void ProcessComment();

  void ProcessOneLineComment();
  void ProcessMultiLineComment();

  void Require(char Expected);

  /// Get current character from input range and move forward.
  char PeekNext();

  /// Get current character from input without moving to the next one.
  char PeekCurrent() const;

  Token MakeToken(std::string Data, TokenType Type) const;

  /// First symbol in buffer.
  const char *BufStart;

  /// Last symbol in buffer (null-terminator).
  const char *BufEnd;

  /// Current symbol to be lexed.
  const char *BufPtr;

  /// Line number (used for error reports).
  unsigned LineNo;

  /// Column number (used for error reports).
  unsigned ColumnNo;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_LEX_LEXER_HPP