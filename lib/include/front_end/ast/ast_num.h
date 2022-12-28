/* ast_num.h - AST node to represent an integer number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_NUM_H
#define WEAK_COMPILER_FRONTEND_AST_AST_NUM_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    int32_t value;
} ast_num_t;

ast_node_t *ast_num_init(int32_t value, uint16_t line_no, uint16_t col_no);
void        ast_num_cleanup(ast_num_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FLOAT_H
