/* ast_array_access.c - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_array_access.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_array_access_init(char *name, ast_node_t *indices, uint16_t line_no, uint16_t col_no)
{
    ast_array_access_t *ast = weak_calloc(1, sizeof(ast_array_access_t));
    ast->name = name;
    ast->indices = indices;
    return ast_node_init(AST_ARRAY_ACCESS, ast, line_no, col_no);
}

void ast_array_access_cleanup(ast_array_access_t *ast)
{
    ast_node_cleanup(ast->indices);
    weak_free(ast->name);
    weak_free(ast);
}