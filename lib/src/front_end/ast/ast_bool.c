/* ast_bool.c - AST node to represent a boolean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_bool.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_bool_init(bool value, uint16_t line_no, uint16_t col_no)
{
    ast_bool_t *ast = weak_calloc(1, sizeof(ast_bool_t));
    ast->value = value;
    return ast_node_init(AST_BOOLEAN_LITERAL, ast, line_no, col_no);
}

void ast_bool_cleanup(ast_bool_t *ast)
{
    weak_free(ast);
}