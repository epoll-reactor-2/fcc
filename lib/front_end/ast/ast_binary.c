/* ast_binary.c - AST node to represent a binary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_binary.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_binary_init(
    tok_type_e  operation,
    ast_node_t *lhs,
    ast_node_t *rhs,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_binary_t *ast = weak_calloc(1, sizeof(ast_binary_t));
    ast->operation = operation;
    ast->lhs = lhs;
    ast->rhs = rhs;
    return ast_node_init(AST_BINARY, ast, line_no, col_no);
}

void ast_binary_cleanup(ast_binary_t *ast)
{
    ast_node_cleanup(ast->lhs);
    ast_node_cleanup(ast->rhs);
    weak_free(ast);
}