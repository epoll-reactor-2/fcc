/* ast_struct_decl.h - AST node to represent a type declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_H

#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    char       *name; /// \note Must be dynamically allocated.
    ast_node_t *decls;
} ast_struct_decl_t;

ast_node_t *ast_struct_decl_init(char *name, ast_node_t *decls, uint16_t line_no, uint16_t col_no);
void        ast_struct_decl_cleanup(ast_struct_decl_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_H