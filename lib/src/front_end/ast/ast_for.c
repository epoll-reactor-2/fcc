/* ast_for.c - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_for.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_for_init(
    ast_node_t *init,
    ast_node_t *condition,
    ast_node_t *increment,
    ast_node_t *body,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_for_t *ast = weak_calloc(1, sizeof(ast_for_t));
    ast->init = init;
    ast->condition = condition;
    ast->increment = increment;
    ast->body = body;
    return ast_node_init(AST_FOR_STMT, ast, line_no, col_no);
}

void ast_for_cleanup(ast_for_t *ast)
{
    if (ast->init)
        ast_node_cleanup(ast->init);

    if (ast->condition)
        ast_node_cleanup(ast->condition);

    if (ast->increment)
        ast_node_cleanup(ast->increment);

    ast_node_cleanup(ast->body);
    weak_free(ast);
}