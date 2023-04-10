/* ast_compound.c - AST node to represent a sequence of nodes.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_compound.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"
#include <stdio.h>

ast_node_t *ast_compound_init(uint64_t size, ast_node_t **stmts, uint16_t line_no, uint16_t col_no)
{
    ast_compound_t *ast = weak_calloc(1, sizeof(ast_compound_t));
    ast->size = size;
    ast->stmts = stmts;
    return ast_node_init(AST_COMPOUND_STMT, ast, line_no, col_no);
}

void ast_compound_cleanup(ast_compound_t *ast)
{
    for (uint64_t i = 0; i < ast->size; ++i) {
        ast_node_cleanup(ast->stmts[i]);
    }

    weak_free(ast->stmts);
    weak_free(ast);
}