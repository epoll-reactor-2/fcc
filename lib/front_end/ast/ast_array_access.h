/* ast_array_access.h - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H
#define WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H

#include <stdbool.h>
#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    char       *name; /// \note Must be dynamically allocated.
    ast_node_t *indices;
} ast_array_access_t;

ast_node_t *ast_array_access_init(char *name, ast_node_t *indices, uint16_t line_no, uint16_t col_no);
void        ast_array_access_cleanup(ast_array_access_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H
