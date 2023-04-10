/* ast_array_decl.h - AST node to represent an array declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_H

#include "front_end/lex/data_type.h"
#include <stdint.h>

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
    /// \note If present, must be dynamically allocated.
    char *type_name;

    /// This stores information about array arity (dimension)
    /// and size for each dimension, e.g.,
    /// for array[1][2][3], ArityList equal to { 1, 2, 3 }.
    ast_node_t *arity_list;

    /// Depth of pointer, like for
    /// int ***ptr[2] indirection level = 3, for
    /// int *ptr[2] = 1, for
    /// int var[2] = 0.
    uint16_t indirection_lvl;
} ast_array_decl_t;

/// \note type_name may be NULL.
ast_node_t *ast_array_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    ast_node_t  *arity_list,
    uint16_t     indirection_lvl,
    uint16_t     line_no,
    uint16_t     col_no
);

void ast_array_decl_cleanup(ast_array_decl_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_H
