/* ast_unary.c - AST node to represent an unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_unary.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"
#include "utility/unreachable.h"

ast_node_t *ast_unary_init(ast_type_e type, tok_type_e operation, ast_node_t *operand, uint16_t line_no, uint16_t col_no)
{
    if (type != AST_PREFIX_UNARY && type != AST_POSTFIX_UNARY) {
        weak_fatal_error("Expected prefix or postfix unary type.");
    }

    ast_unary_t *ast = weak_calloc(1, sizeof(ast_unary_t));
    ast->operation = operation;
    ast->operand = operand;
    return ast_node_init(type, ast, line_no, col_no);
}

void ast_unary_cleanup(ast_unary_t *ast)
{
    ast_node_cleanup(ast->operand);
    weak_free(ast);
}