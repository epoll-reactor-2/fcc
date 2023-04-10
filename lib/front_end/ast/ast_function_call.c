/* ast_function_call.h - AST node to represent a function call statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_function_call.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_function_call_init(
    char       *name,
    ast_node_t *args,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_function_call_t *ast = weak_calloc(1, sizeof(ast_function_call_t));
    ast->name = name;
    ast->args = args;
    return ast_node_init(AST_FUNCTION_CALL, ast, line_no, col_no);
}

void ast_function_call_cleanup(ast_function_call_t *ast)
{
    ast_node_cleanup(ast->args);
    weak_free(ast->name);
    weak_free(ast);
}