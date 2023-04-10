/* ast_binary.h - AST node to represent a binary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BINARY_H
#define WEAK_COMPILER_FRONTEND_AST_AST_BINARY_H

#include "front_end/lex/tok_type.h"
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    tok_type_e  operation;
    ast_node_t *lhs;
    ast_node_t *rhs;
} ast_binary_t;

ast_node_t *ast_binary_init(
    tok_type_e  operation,
    ast_node_t *lhs,
    ast_node_t *rhs,
    uint16_t    line_no,
    uint16_t    col_no
);

void ast_binary_cleanup(ast_binary_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BINARY_H