/* ast_while.h - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_WHILE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_WHILE_H

#include "front_end/ast/ast_compound.h"

typedef struct ast_node_t ast_node_t;

typedef struct {
    ast_node_t *condition;
    ast_node_t *body;
} ast_while_t;

ast_node_t *ast_while_init(ast_node_t *condition, ast_node_t *body, uint16_t line_no, uint16_t col_no);
void        ast_while_cleanup(ast_while_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_WHILE_H
