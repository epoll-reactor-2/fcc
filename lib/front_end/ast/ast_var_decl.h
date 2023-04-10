/* ast_var_decl.h - AST node to represent a variable declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H

#include "front_end/ast/ast_compound.h"
#include "front_end/lex/data_type.h"

typedef struct ast_node_t ast_node_t;

typedef struct {
    /// Data type of array.
    data_type_e dt;

    /// Variable name.
    ///
    /// \note Must be dynamically allocated.
    char *name;

    /// Optional type name for arrays of structure type.
    ///
    /// \note - If present, must be dynamically allocated.
    ///       - May be NULL. If so, this statement represents
    ///         primitive type declaration.
    char *type_name;

    /// Depth of pointer, like for
    /// int ***ptr indirection level = 3, for
    /// int *ptr = 1, for
    /// int var = 0.
    uint16_t indirection_lvl;

    /// Declaration body (expression after `=`).
    ///
    /// \note May be NULL. If so, this statement represents declarator
    ///       without initializer.
    ast_node_t *body;
} ast_var_decl_t;

/// \note type_name may be NULL.
ast_node_t *ast_var_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    uint16_t     indirection_lvl,
    ast_node_t  *body,
    uint16_t     line_no,
    uint16_t     col_no
);

void ast_var_decl_cleanup(ast_var_decl_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H
