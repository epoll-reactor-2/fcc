/* ast_var_decl.c - AST node to represent a variable declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_var_decl.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_var_decl_init(
    data_type_e  dt,
    char        *name,
    char        *type_name,
    uint16_t     indirection_lvl,
    ast_node_t  *body,
    uint16_t     line_no,
    uint16_t     col_no
) {
    ast_var_decl_t *ast = weak_calloc(1, sizeof(ast_var_decl_t));
    ast->dt = dt;
    ast->name = name;
    ast->type_name = type_name;
    ast->body = body;
    ast->indirection_lvl = indirection_lvl;
    return ast_node_init(AST_VAR_DECL, ast, line_no, col_no);
}

void ast_var_decl_cleanup(ast_var_decl_t *ast)
{
    weak_free(ast->name);

    if (ast->type_name)
        weak_free(ast->type_name);

    if (ast->body)
        ast_node_cleanup(ast->body);

    weak_free(ast);
}