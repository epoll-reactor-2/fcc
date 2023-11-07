/* struct tokenype.h - List of all token types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_LEX_TOK_TYPE_H
#define WEAK_COMPILER_FRONTEND_LEX_TOK_TYPE_H

#include "util/compiler.h"

enum token_type {
    /** Keywords. */
    TOK_BOOL,
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
    TOK_STRUCT,
    TOK_TRUE,
    TOK_VOID,
    TOK_WHILE,

    /** Literals. */
    TOK_CHAR_LITERAL,
    TOK_INTEGRAL_LITERAL,
    TOK_FLOATING_POINT_LITERAL,
    TOK_STRING_LITERAL,
    TOK_SYMBOL,

    /** Operators. */
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
    TOK_DOT,                 // .
    TOK_COMMA,               // ,
    TOK_COLON,               // :
    TOK_SEMICOLON,           // ;
    TOK_NOT,                 // !
    TOK_OPEN_BOX_BRACKET,    // [
    TOK_CLOSE_BOX_BRACKET,   // ]
    TOK_OPEN_CURLY_BRACKET,  // {
    TOK_CLOSE_CURLY_BRACKET, // }
    TOK_OPEN_PAREN,          // (
    TOK_CLOSE_PAREN          // )
};

/** \return String representation of the token. Don't
            apply free() to the result.
   
    \note   weak_unreachable() called on unknown integer value of t. */
__weak_wur const char *tok_to_string(enum token_type t);

/** \return Token type based on its character value.
   
    \note   weak_unreachable() called on unknown char. */
__weak_wur enum token_type tok_char_to_tok(char c);

#endif // WEAK_COMPILER_FRONTEND_LEX_TOK_TYPE_H