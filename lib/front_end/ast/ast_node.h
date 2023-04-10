/* ast_node.h - Base AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_NODE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_NODE_H

#include "front_end/ast/ast_type.h"
#include <stdint.h>

/// Typed pointer to AST node of any type.
///
/// Each implemented AST node must have methods
/// - ast_%name%_init(...)
/// - ast_%name%_cleanup(...)
/// .
///
/// \note Cleanup methods for all AST's located in ast_cleanup.c
typedef struct ast_node_t {
    ast_type_e  type;
    void       *ast;
    uint16_t    line_no;
    uint16_t    col_no;
} ast_node_t;

/// Allocate AST node of given type.
ast_node_t *ast_node_init(ast_type_e type, void *ast, uint16_t line_no, uint16_t col_no);

/// Cleanup whole given AST tree through call
/// to proper functions for each node type.
///
/// \note Implemented in ast_cleanup.c file because for that
///       needed all AST header files.
void ast_node_cleanup(ast_node_t *ast);

#endif // WEAK_COMPILER_FRONTEND_AST_AST_NODE_H
