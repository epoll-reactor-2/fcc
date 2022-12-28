/* ast_continue.h - AST node to represent a continue statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_CONTINUE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_CONTINUE_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    /// Empty.
} ast_continue_t;

ast_node_t *ast_continue_init(uint16_t line_no, uint16_t col_no);
void        ast_continue_cleanup(ast_continue_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_CONTINUE_H
