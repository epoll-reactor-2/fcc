/* ast_if.c - AST node to represent an if statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_if.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_if_init(
    ast_node_t *condition,
    ast_node_t *body,
    ast_node_t *else_body,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_if_t *ast = weak_calloc(1, sizeof(ast_if_t));
    ast->condition = condition;
    ast->body = body;
    ast->else_body = else_body;
    return ast_node_init(AST_IF_STMT, ast, line_no, col_no);
}

void ast_if_cleanup(ast_if_t *ast)
{
    ast_node_cleanup(ast->condition);
    ast_node_cleanup(ast->body);

    if (ast->else_body)
        ast_node_cleanup(ast->else_body);

    weak_free(ast);
}