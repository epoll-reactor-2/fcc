/* ast_type.h - List of all AST types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef FCC_FRONTEND_AST_AST_TYPE_H
#define FCC_FRONTEND_AST_AST_TYPE_H

enum ast_type {
    /** Literals. */
    AST_CHAR,
    AST_INT,
    AST_FLOAT,
    AST_STRING,
    AST_BOOL,

    /** Variable reference. */
    AST_SYMBOL,

    /** Declarations. */
    AST_VAR_DECL,
    AST_ARRAY_DECL,
    AST_STRUCT_DECL,

    /** Iteration statements. */
    AST_BREAK_STMT,
    AST_CONTINUE_STMT,

    /** Operators. */
    AST_BINARY,
    AST_PREFIX_UNARY,
    AST_POSTFIX_UNARY,
    AST_ARRAY_ACCESS,
    AST_MEMBER,

    /** Selection statements. */
    AST_IF_STMT,

    /** Loops. */
    AST_FOR_STMT,
    AST_FOR_RANGE_STMT,
    AST_WHILE_STMT,
    AST_DO_WHILE_STMT,

    /** Jump statements. */
    AST_RETURN_STMT,

    /** Block statements. */
    AST_COMPOUND_STMT,

    /** Functions. */
    AST_FUNCTION_DECL,
    AST_FUNCTION_CALL,

    /** Implicit type conversion. */
    AST_IMPLICIT_CAST
};

/** \return String representation of the AST type. Don't
             apply free() to the result.

    \note   fcc_unreachable() called on unknown integer value of t. */
const char *ast_type_to_string(enum ast_type t);

#endif // FCC_FRONTEND_AST_AST_TYPE_H