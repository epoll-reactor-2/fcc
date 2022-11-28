/* ASTType.cpp - List of all AST types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTType.h"
#include "Utility/Diagnostic.h"

const char *weak::ASTTypeToString(ASTType T) {
  switch (T) {
  case AST_CHAR_LITERAL:           return "AST_CHAR_LITERAL";
  case AST_INTEGER_LITERAL:        return "AST_INTEGER_LITERAL";
  case AST_FLOATING_POINT_LITERAL: return "AST_FLOATING_POINT_LITERAL";
  case AST_STRING_LITERAL:         return "AST_STRING_LITERAL";
  case AST_BOOLEAN_LITERAL:        return "AST_BOOLEAN_LITERAL";
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
  case AST_MEMBER_ACCESS:          return "AST_MEMBER_ACCESS";
  case AST_IF_STMT:                return "AST_IF_STMT";
  case AST_FOR_STMT:               return "AST_FOR_STMT";
  case AST_WHILE_STMT:             return "AST_WHILE_STMT";
  case AST_DO_WHILE_STMT:          return "AST_DO_WHILE_STMT";
  case AST_RETURN_STMT:            return "AST_RETURN_STMT";
  case AST_COMPOUND_STMT:          return "AST_COMPOUND_STMT";
  case AST_FUNCTION_DECL:          return "AST_FUNCTION_DECL";
  case AST_FUNCTION_CALL:          return "AST_FUNCTION_CALL";
  case AST_FUNCTION_PROTOTYPE:     return "AST_FUNCTION_PROTOTYPE";
  default:                         Unreachable();
  }
}