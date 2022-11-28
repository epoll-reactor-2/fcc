/* Token.h - Definition of token.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_TOKEN_H
#define WEAK_COMPILER_FRONTEND_LEX_TOKEN_H

#include "FrontEnd/Lex/TokenType.h"
#include <string>

namespace weak {

const char *TokenToString(TokenType Type);
TokenType CharToToken(char T);

struct Token {
  Token(
    std::string TheData,
    TokenType   TheType,
    unsigned    TheLineNo,
    unsigned    TheColumnNo
  );

  /// Judge if token has type denoted by char.
  bool Is(char Token) const;

  bool Is(TokenType T) const;

  bool operator==(const Token &RHS) const;

  bool operator!=(const Token &RHS) const;

  /// Data if any (digits, symbols, literals).
  std::string Data;

  /// Token type.
  TokenType Type;

  /// Position in source text.
  unsigned LineNo;

  /// Position in source text.
  unsigned ColumnNo;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_LEX_TOKEN_H