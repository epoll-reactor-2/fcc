/* ast_char.h - AST node to represent a single character.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_CHAR_H
#define WEAK_COMPILER_FRONTEND_AST_AST_CHAR_H

#include <stdint.h>

typedef struct ast_node_t ast_node_t;

typedef struct {
    char value;
} ast_char_t;

ast_node_t *ast_char_init(char value, uint16_t line_no, uint16_t col_no);
void        ast_char_cleanup(ast_char_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_CHAR_H
