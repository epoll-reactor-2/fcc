/* ast_bool.h - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BOOL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_BOOL_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    bool value;
} ast_bool_t;

ast_node_t *ast_bool_init(bool value, uint16_t line_no, uint16_t col_no);
void        ast_bool_cleanup(ast_bool_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BOOL_H
