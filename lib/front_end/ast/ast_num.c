/* ast_num.c - AST node to represent an integer literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_num.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_num_init(int32_t value, uint16_t line_no, uint16_t col_no)
{
    ast_num_t *ast = weak_calloc(1, sizeof(ast_num_t));
    ast->value = value;
    return ast_node_init(AST_INTEGER_LITERAL, ast, line_no, col_no);
}

void ast_num_cleanup(ast_num_t *ast)
{
    weak_free(ast);
}