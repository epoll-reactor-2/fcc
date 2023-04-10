/* ast_return.h - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_RETURN_H
#define WEAK_COMPILER_FRONTEND_AST_AST_RETURN_H

#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    ast_node_t *operand; /// \note May be NULL to represent return from void function.
} ast_return_t;

ast_node_t *ast_return_init(ast_node_t *operand, uint16_t line_no, uint16_t col_no);
void        ast_return_cleanup(ast_return_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_RETURN_H