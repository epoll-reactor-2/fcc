/* ast_char.c - AST node to represent a charean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_char.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_char_init(char value, uint16_t line_no, uint16_t col_no)
{
    ast_char_t *ast = weak_calloc(1, sizeof(ast_char_t));
    ast->value = value;
    return ast_node_init(AST_CHAR_LITERAL, ast, line_no, col_no);
}

void ast_char_cleanup(ast_char_t *ast)
{
    weak_free(ast);
}