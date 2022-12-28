/* ast_symbol.h - AST node to represent a variable name.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_SYMBOL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_SYMBOL_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    char *value; /// \note Must be dynamically allocated.
} ast_symbol_t;

ast_node_t *ast_symbol_init(char *value, uint16_t line_no, uint16_t col_no);
void        ast_symbol_cleanup(ast_symbol_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_SYMBOL_H
