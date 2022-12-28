/* ast_node.c - Base AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_node_init(ast_type_e type, void *ast, uint16_t line_no, uint16_t col_no)
{
    ast_node_t *node = weak_calloc(1, sizeof(ast_node_t));
    node->type = type;
    node->ast = ast;
    node->line_no = line_no;
    node->col_no = col_no;
    return node;
}