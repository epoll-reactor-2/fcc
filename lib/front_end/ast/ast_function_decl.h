/* ast_function_decl.h - AST node to represent a function declaration
 *                       or prototype.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H

#include "front_end/lex/data_type.h"
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    data_type_e  data_type;
    char        *name; /// \note Must be dynamically allocated.
    ast_node_t  *args;
    ast_node_t  *body; /// \note May be NULL. If so, this statement represents
                       ///       function prototype.
} ast_function_decl_t;

ast_node_t *ast_function_decl_init(
    data_type_e  data_type,
    char        *name,
    ast_node_t  *args,
    ast_node_t  *body,
    uint16_t     line_no,
    uint16_t     col_no
);

void ast_function_decl_cleanup(ast_function_decl_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H