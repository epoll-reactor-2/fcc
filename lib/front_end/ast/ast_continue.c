/* ast_continue.c - AST node to represent a continue statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_continue.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_continue_init(uint16_t line_no, uint16_t col_no)
{
    ast_continue_t *ast = weak_calloc(1, sizeof(ast_continue_t));
    return ast_node_init(AST_CONTINUE_STMT, ast, line_no, col_no);
}

void ast_continue_cleanup(ast_continue_t *ast)
{
    weak_free(ast);
}