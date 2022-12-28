/* ast_member.c - AST node to represent a struct member access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_member.h"
#include "front_end/ast/ast_node.h"
#include "utility/alloc.h"

ast_node_t *ast_member_init(
    ast_node_t *structure,
    ast_node_t *member,
    uint16_t    line_no,
    uint16_t    col_no
) {
    ast_member_t *ast = weak_calloc(1, sizeof(ast_member_t));
    ast->structure = structure;
    ast->member = member;
    return ast_node_init(AST_MEMBER, ast, line_no, col_no);
}

void ast_member_cleanup(ast_member_t *ast)
{
    ast_node_cleanup(ast->member);
    ast_node_cleanup(ast->structure);
    weak_free(ast);
}