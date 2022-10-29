/* Token.h - List of all token types and token definition itself.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_TOKEN_H
#define WEAK_COMPILER_FRONTEND_LEX_TOKEN_H

#include <string>

namespace weak {

enum TokenType {
  // Keywords.
  TOK_BOOLEAN,
  TOK_BREAK,
  TOK_CHAR,
  TOK_CONTINUE,
  TOK_DO,
  TOK_ELSE,
  TOK_FALSE,
  TOK_FLOAT,
  TOK_FOR,
  TOK_IF,
  TOK_INT,
  TOK_RETURN,
  TOK_STRING,
  TOK_TRUE,
  TOK_VOID,
  TOK_WHILE,
  TOK_STRUCT,

  // Literals.
  TOK_CHAR_LITERAL,
  TOK_INTEGRAL_LITERAL,
  TOK_FLOATING_POINT_LITERAL,
  TOK_STRING_LITERAL,
  TOK_SYMBOL,

  // Operators.
  TOK_ASSIGN,              // =
  TOK_MUL_ASSIGN,          // *=
  TOK_DIV_ASSIGN,          // /=
  TOK_MOD_ASSIGN,          // %=
  TOK_PLUS_ASSIGN,         // +=
  TOK_MINUS_ASSIGN,        // -=
  TOK_SHL_ASSIGN,          // <<=
  TOK_SHR_ASSIGN,          // >>=
  TOK_BIT_AND_ASSIGN,      // &=
  TOK_BIT_OR_ASSIGN,       // |=
  TOK_XOR_ASSIGN,          // ^=
  TOK_AND,                 // &&
  TOK_OR,                  // ||
  TOK_XOR,                 // ^
  TOK_BIT_AND,             // &
  TOK_BIT_OR,              // |
  TOK_EQ,                  // ==
  TOK_NEQ,                 // !=
  TOK_GT,                  // >
  TOK_LT,                  // <
  TOK_GE,                  // >=
  TOK_LE,                  // <=
  TOK_SHL,                 // <<
  TOK_SHR,                 // >>
  TOK_PLUS,                // +
  TOK_MINUS,               // -
  TOK_STAR,                // *
  TOK_SLASH,               // /
  TOK_MOD,                 // %
  TOK_INC,                 // ++
  TOK_DEC,                 // --
  TOK_COMMA,               // ,
  TOK_SEMICOLON,           // ;
  TOK_NOT,                 // !
  TOK_OPEN_BOX_BRACKET,    // [
  TOK_CLOSE_BOX_BRACKET,   // ]
  TOK_OPEN_CURLY_BRACKET,  // {
  TOK_CLOSE_CURLY_BRACKET, // }
  TOK_OPEN_PAREN,          // (
  TOK_CLOSE_PAREN          // )
};

const char *TokenToString(TokenType Type);
TokenType CharToToken(char T);

struct Token {
  Token(std::string TheData, TokenType TheType, unsigned TheLineNo,
        unsigned TheColumnNo);

  /// Judge if token has type denoted by char.
  bool Is(char Token) const;

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