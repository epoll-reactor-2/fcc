/* ast_while.c - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_while.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_while_init(ast_node_t *condition, ast_node_t *body, uint16_t line_no, uint16_t col_no)
{
    ast_while_t *ast = weak_calloc(1, sizeof(ast_while_t));
    ast->condition = condition;
    ast->body = body;
    return ast_node_init(AST_WHILE_STMT, ast, line_no, col_no);
}

void ast_while_cleanup(ast_while_t *ast)
{
    ast_node_cleanup(ast->condition);
    ast_node_cleanup(ast->body);
    weak_free(ast);
}
