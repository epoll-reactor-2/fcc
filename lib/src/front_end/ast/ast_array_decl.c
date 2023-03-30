/* ast_array_decl.c - AST node to represent array declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_array_decl.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_array_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    ast_node_t  *arity_list,
    uint16_t     indirection_lvl,
    uint16_t     line_no,
    uint16_t     col_no
) {
    ast_array_decl_t *ast = weak_calloc(1, sizeof(ast_array_decl_t));
    ast->dt = dt;
    ast->name = name;
    ast->type_name = type_name;
    ast->arity_list = arity_list;
    ast->indirection_lvl = indirection_lvl;
    return ast_node_init(AST_ARRAY_DECL, ast, line_no, col_no);
}

void ast_array_decl_cleanup(ast_array_decl_t *ast)
{
    ast_node_cleanup(ast->arity_list);
    if (ast->type_name)
        weak_free(ast->type_name);
    weak_free(ast->name);
    weak_free(ast);
}