/* ast_break.h - AST node to represent a break statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BREAK_H
#define WEAK_COMPILER_FRONTEND_AST_AST_BREAK_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    /// Empty.
} ast_break_t;

ast_node_t *ast_break_init(uint16_t line_no, uint16_t col_no);
void        ast_break_cleanup(ast_break_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BREAK_H
