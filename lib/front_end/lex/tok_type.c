/* tok_type.c - String conversion function for the token enum.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/tok_type.h"
#include "util/unreachable.h"

const char *tok_to_string(enum token_type t)
{
    switch (t) {
    case TOK_BOOL:                   return "bool";
    case TOK_BREAK:                  return "break";
    case TOK_CHAR:                   return "char";
    case TOK_CONTINUE:               return "continue";
    case TOK_DO:                     return "do";
    case TOK_ELSE:                   return "else";
    case TOK_FALSE:                  return "false";
    case TOK_FLOAT:                  return "float";
    case TOK_FOR:                    return "for";
    case TOK_IF:                     return "if";
    case TOK_INT:                    return "int";
    case TOK_RETURN:                 return "return";
    case TOK_STRUCT:                 return "struct";
    case TOK_TRUE:                   return "true";
    case TOK_VOID:                   return "void";
    case TOK_WHILE:                  return "while";
    case TOK_CHAR_LITERAL:           return "char literal";
    case TOK_INT_LITERAL:            return "int literal";
    case TOK_FLOAT_LITERAL:          return "float literal";
    case TOK_STRING_LITERAL:         return "string literal";
    case TOK_SYMBOL:                 return "symbol";
    case TOK_ASSIGN:                 return "=";
    case TOK_MUL_ASSIGN:             return "*=";
    case TOK_DIV_ASSIGN:             return "/=";
    case TOK_MOD_ASSIGN:             return "%=";
    case TOK_PLUS_ASSIGN:            return "+=";
    case TOK_MINUS_ASSIGN:           return "-=";
    case TOK_SHL_ASSIGN:             return "<<=";
    case TOK_SHR_ASSIGN:             return ">>=";
    case TOK_BIT_AND_ASSIGN:         return "&=";
    case TOK_BIT_OR_ASSIGN:          return "|=";
    case TOK_XOR_ASSIGN:             return "^=";
    case TOK_AND:                    return "&&";
    case TOK_OR:                     return "||";
    case TOK_XOR:                    return "^";
    case TOK_BIT_AND:                return "&";
    case TOK_BIT_OR:                 return "|";
    case TOK_EQ:                     return "==";
    case TOK_NEQ:                    return "!=";
    case TOK_GT:                     return ">";
    case TOK_LT:                     return "<";
    case TOK_GE:                     return ">=";
    case TOK_LE:                     return "<=";
    case TOK_SHL:                    return "<<";
    case TOK_SHR:                    return ">>";
    case TOK_PLUS:                   return "+";
    case TOK_MINUS:                  return "-";
    case TOK_STAR:                   return "*";
    case TOK_SLASH:                  return "/";
    case TOK_MOD:                    return "%";
    case TOK_INC:                    return "++";
    case TOK_DEC:                    return "--";
    case TOK_DOT:                    return ".";
    case TOK_COMMA:                  return ",";
    case TOK_COLON:                  return ":";
    case TOK_SEMICOLON:              return ";";
    case TOK_NOT:                    return "!";
    case TOK_OPEN_BOX_BRACKET:       return "[";
    case TOK_CLOSE_BOX_BRACKET:      return "]";
    case TOK_OPEN_CURLY_BRACKET:     return "{";
    case TOK_CLOSE_CURLY_BRACKET:    return "}";
    case TOK_OPEN_PAREN:             return "(";
    case TOK_CLOSE_PAREN:            return ")";
    default:
        weak_unreachable("Unknown token type (numeric: %d).", t);
    }
}

enum token_type tok_char_to_tok(char c)
{
    switch (c) {
    case '=': return TOK_ASSIGN;
    case '^': return TOK_XOR;
    case '&': return TOK_BIT_AND;
    case '|': return TOK_BIT_OR;
    case '>': return TOK_GT;
    case '<': return TOK_LT;
    case '+': return TOK_PLUS;
    case '-': return TOK_MINUS;
    case '*': return TOK_STAR;
    case '/': return TOK_SLASH;
    case '%': return TOK_MOD;
    case '.': return TOK_DOT;
    case ',': return TOK_COMMA;
    case ':': return TOK_COLON;
    case ';': return TOK_SEMICOLON;
    case '!': return TOK_NOT;
    case '[': return TOK_OPEN_BOX_BRACKET;
    case ']': return TOK_CLOSE_BOX_BRACKET;
    case '{': return TOK_OPEN_CURLY_BRACKET;
    case '}': return TOK_CLOSE_CURLY_BRACKET;
    case '(': return TOK_OPEN_PAREN;
    case ')': return TOK_CLOSE_PAREN;
    default:
        weak_unreachable("Unknown character operation (char: `%c`).", c);
    }
}