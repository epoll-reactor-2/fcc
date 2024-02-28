/* ast_type.c - String conversion function for the AST enum.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_type.h"
#include "util/unreachable.h"

const char *ast_type_to_string(enum ast_type t) {
    switch (t) {
    case AST_CHAR:                   return "AST_CHAR";
    case AST_INT:                    return "AST_INT";
    case AST_FLOAT:                  return "AST_FLOAT";
    case AST_STRING:                 return "AST_STRING";
    case AST_BOOL:                   return "AST_BOOL";
    case AST_SYMBOL:                 return "AST_VAR_DECL";
    case AST_VAR_DECL:               return "AST_VAR_DECL";
    case AST_ARRAY_DECL:             return "AST_ARRAY_DECL";
    case AST_STRUCT_DECL:            return "AST_STRUCT_DECL";
    case AST_BREAK_STMT:             return "AST_BREAK_STMT";
    case AST_CONTINUE_STMT:          return "AST_CONTINUE_STMT";
    case AST_BINARY:                 return "AST_BINARY";
    case AST_PREFIX_UNARY:           return "AST_PREFIX_UNARY";
    case AST_POSTFIX_UNARY:          return "AST_POSTFIX_UNARY";
    case AST_ARRAY_ACCESS:           return "AST_ARRAY_ACCESS";
    case AST_MEMBER:                 return "AST_MEMBER";
    case AST_IF_STMT:                return "AST_IF_STMT";
    case AST_FOR_STMT:               return "AST_FOR_STMT";
    case AST_WHILE_STMT:             return "AST_WHILE_STMT";
    case AST_DO_WHILE_STMT:          return "AST_DO_WHILE_STMT";
    case AST_RETURN_STMT:            return "AST_RETURN_STMT";
    case AST_COMPOUND_STMT:          return "AST_COMPOUND_STMT";
    case AST_FUNCTION_DECL:          return "AST_FUNCTION_DECL";
    case AST_FUNCTION_CALL:          return "AST_FUNCTION_CALL";
    case AST_IMPLICIT_CAST:          return "AST_IMPLICIT_CAST";
    default:                         weak_unreachable("Should not reach there.");
    }
}
