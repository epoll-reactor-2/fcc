/* ast_function_decl.h - AST node to represent a function call statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_CALL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_CALL_H

#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    char       *name; /// \note Must be dynamically allocated.
    ast_node_t *args;
} ast_function_call_t;

ast_node_t *ast_function_call_init(
    char       *name,
    ast_node_t *args,
    uint16_t    line_no,
    uint16_t    col_no
);

void ast_function_call_cleanup(ast_function_call_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_CALL_H