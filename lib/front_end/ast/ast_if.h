/* ast_if.h - AST node to represent an if statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_IF_H
#define WEAK_COMPILER_FRONTEND_AST_AST_IF_H

#include "front_end/ast/ast_compound.h"

typedef struct ast_node_t ast_node_t;

typedef struct {
    ast_node_t *condition;
    ast_node_t *body;
    ast_node_t *else_body; /// \note May be NULL.
} ast_if_t;

ast_node_t *ast_if_init(
    ast_node_t *condition,
    ast_node_t *body,
    ast_node_t *else_body,
    uint16_t    line_no,
    uint16_t    col_no
);

void ast_if_cleanup(ast_if_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_IF_H
