/* ast_float.h - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FLOAT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FLOAT_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    float value;
} ast_float_t;

ast_node_t *ast_float_init(float value, uint16_t line_no, uint16_t col_no);
void        ast_float_cleanup(ast_float_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FLOAT_H
