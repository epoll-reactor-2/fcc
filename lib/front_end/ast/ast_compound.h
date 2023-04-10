/* ast_compound.h - AST node to represent a sequence of nodes.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_H
#define WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    uint64_t     size;
    ast_node_t **stmts;
} ast_compound_t;

ast_node_t *ast_compound_init(uint64_t size, ast_node_t **stmts, uint16_t line_no, uint16_t col_no);
void        ast_compound_cleanup(ast_compound_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_H
