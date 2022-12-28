/* ast_break.c - AST node to represent a break statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_break.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_break_init(uint16_t line_no, uint16_t col_no)
{
    ast_break_t *ast = weak_calloc(1, sizeof(ast_break_t));
    return ast_node_init(AST_BREAK_STMT, ast, line_no, col_no);
}

void ast_break_cleanup(ast_break_t *ast)
{
    weak_free(ast);
}