/* ast_return.c - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_return.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_return_init(ast_node_t *operand, uint16_t line_no, uint16_t col_no)
{
    ast_return_t *ast = weak_calloc(1, sizeof(ast_return_t));
    ast->operand = operand;
    return ast_node_init(AST_RETURN_STMT, ast, line_no, col_no);
}

void ast_return_cleanup(ast_return_t *ast)
{
    if (ast->operand)
        ast_node_cleanup(ast->operand);

    weak_free(ast);
}