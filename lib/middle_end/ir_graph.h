/* ir_graph.h - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H
#define WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H

#include <stdint.h>
#include <stdbool.h>

struct ir;
struct ir_node;

/// Build directed graph from the IR list.
///
/// There is no output since all what this function does
/// is setting up pointers named `next` on each IR statement.
/// So the result of such linking is adjacency list, which
/// is implicitly contained in IR nodes.
///
/// \note Done by default in ir_gen().
///
/// \param ir     List of function declarations.
///               Linking is performed separately for each
///               function.
void ir_link(struct ir *ir);

/// Traverse IR graph.
///
/// Reminder:
///     struct ir_func_decl *decl = ir->decls[0].ir;
///     ir_traverse(&decl->body[0]);
///
/// \todo Make this function do anything useful.
///
/// \param stmt First statement in a function.
void ir_traverse(struct ir_node *ir);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H