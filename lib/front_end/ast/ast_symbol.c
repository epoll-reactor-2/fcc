/* ast_symbol.c - AST node to represent a variable name.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_symbol.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_symbol_init(char *value, uint16_t line_no, uint16_t col_no)
{
    ast_symbol_t *ast = weak_calloc(1, sizeof(ast_symbol_t));
    ast->value = value;
    return ast_node_init(AST_SYMBOL, ast, line_no, col_no);
}

void ast_symbol_cleanup(ast_symbol_t *ast)
{
    weak_free(ast->value);
    weak_free(ast);
}