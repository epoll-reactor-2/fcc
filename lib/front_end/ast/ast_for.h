/* ast_for.h - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FOR_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FOR_H

#include "front_end/ast/ast_compound.h"

typedef struct ast_node_t ast_node_t;

typedef struct {
    ast_node_t *init; /// \note May be NULL.
    ast_node_t *condition; /// \note May be NULL.
    ast_node_t *increment; /// \note May be NULL.
    ast_node_t *body;
} ast_for_t;

ast_node_t *ast_for_init(
    ast_node_t *init,
    ast_node_t *condition,
    ast_node_t *increment,
    ast_node_t *body,
    uint16_t    line_no,
    uint16_t    col_no
);

void ast_for_cleanup(ast_for_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FOR_H
