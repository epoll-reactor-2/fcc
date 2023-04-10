/* ast_float.c - AST node to represent a floatean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_float.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_float_init(float value, uint16_t line_no, uint16_t col_no)
{
    ast_float_t *ast = weak_calloc(1, sizeof(ast_float_t));
    ast->value = value;
    return ast_node_init(AST_FLOATING_POINT_LITERAL, ast, line_no, col_no);
}

void ast_float_cleanup(ast_float_t *ast)
{
    weak_free(ast);
}