/* ast_struct_decl.c - AST node to represent a type declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_struct_decl.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_struct_decl_init(char *name, ast_node_t *decls, uint16_t line_no, uint16_t col_no)
{
    ast_struct_decl_t *ast = weak_calloc(1, sizeof(ast_struct_decl_t));
    ast->name = name;
    ast->decls = decls;
    return ast_node_init(AST_STRUCT_DECL, ast, line_no, col_no);
}

void ast_struct_decl_cleanup(ast_struct_decl_t *ast)
{
    ast_node_cleanup(ast->decls);
    weak_free(ast->name);
    weak_free(ast);
}