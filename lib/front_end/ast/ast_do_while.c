/* ast_do_while.c - AST node to represent a do-while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_do_while.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_do_while_init(ast_node_t *body, ast_node_t *condition, uint16_t line_no, uint16_t col_no)
{
    ast_do_while_t *ast = weak_calloc(1, sizeof(ast_do_while_t));
    ast->body = body;
    ast->condition = condition;
    return ast_node_init(AST_DO_WHILE_STMT, ast, line_no, col_no);
}

void ast_do_while_cleanup(ast_do_while_t *ast)
{
    ast_node_cleanup(ast->body);
    ast_node_cleanup(ast->condition);
    weak_free(ast);
}
