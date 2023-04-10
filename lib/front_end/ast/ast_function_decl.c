/* ast_function_decl.h - AST node to represent a function declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_function_decl.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_function_decl_init(
    data_type_e data_type,
    char       *name,
    ast_node_t *args,
    ast_node_t *body,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_function_decl_t *ast = weak_calloc(1, sizeof(ast_function_decl_t));
    ast->data_type = data_type;
    ast->name = name;
    ast->args = args;
    ast->body = body;
    return ast_node_init(AST_FUNCTION_DECL, ast, line_no, col_no);
}

void ast_function_decl_cleanup(ast_function_decl_t *ast)
{
    ast_node_cleanup(ast->args);
    if (ast->body)
        ast_node_cleanup(ast->body);
    weak_free(ast->name);
    weak_free(ast);
}