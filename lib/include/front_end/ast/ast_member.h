/* ast_member.h - AST node to represent a struct member access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_MEMBER_H
#define WEAK_COMPILER_FRONTEND_AST_AST_MEMBER_H

#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    /// This represents left side of member operator.
    /// May represent ast_symbol_t, ast_unary_t and so on.
    ast_node_t *structure;
    /// This represents right side of member operator.
    /// May represent ast_member_t and form nested operator.
    ast_node_t *member;
} ast_member_t;

ast_node_t *ast_member_init(
    ast_node_t *structure,
    ast_node_t *member,
    uint16_t    line_no,
    uint16_t    col_no
);

void ast_member_cleanup(ast_member_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_MEMBER_H