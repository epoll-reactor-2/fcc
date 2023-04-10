/* ast_string.h - AST node to represent a string literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_STRING_H
#define WEAK_COMPILER_FRONTEND_AST_AST_STRING_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    char *value; /// \note Must be dynamically allocated.
} ast_string_t;

ast_node_t *ast_string_init(char *value, uint16_t line_no, uint16_t col_no);
void        ast_string_cleanup(ast_string_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_STRING_H
