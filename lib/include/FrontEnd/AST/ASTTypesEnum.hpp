/* ASTTypesEnum.hpp - List of all AST types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_TYPES_ENUM_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_TYPES_ENUM_HPP

namespace weak {

enum ASTType {
  // Literals.
  AST_CHAR_LITERAL,
  AST_INTEGER_LITERAL,
  AST_FLOATING_POINT_LITERAL,
  AST_STRING_LITERAL,
  AST_BOOLEAN_LITERAL,

  // Variable reference.
  AST_SYMBOL,

  // Declarations.
  AST_VAR_DECL,
  AST_ARRAY_DECL,
  AST_STRUCT_DECL,

  // Iteration statements.
  AST_BREAK_STMT,
  AST_CONTINUE_STMT,

  // Operators.
  AST_BINARY,
  AST_PREFIX_UNARY,
  AST_POSTFIX_UNARY,
  AST_ARRAY_ACCESS,

  // Branches.
  AST_IF_STMT,

  // Loops.
  AST_FOR_STMT,
  AST_WHILE_STMT,
  AST_DO_WHILE_STMT,

  // Jump statements.
  AST_RETURN_STMT,

  // Body for block statements.
  AST_COMPOUND_STMT,

  // Functions.
  AST_FUNCTION_DECL,
  AST_FUNCTION_CALL,
  AST_FUNCTION_PROTOTYPE
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_TYPES_ENUM_HPP