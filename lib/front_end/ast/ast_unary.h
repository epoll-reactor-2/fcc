/* ast_unary.h - AST node to represent an unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_UNARY_H
#define WEAK_COMPILER_FRONTEND_AST_AST_UNARY_H

#include "front_end/ast/ast_type.h"
#include "front_end/lex/tok_type.h"
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    ast_type_e  type; /// Prefix or postfix.
    tok_type_e  operation;
    ast_node_t *operand;
} ast_unary_t;

ast_node_t *ast_unary_init(ast_type_e type, tok_type_e operation, ast_node_t *operand, uint16_t line_no, uint16_t col_no);
void        ast_unary_cleanup(ast_unary_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_UNARY_H