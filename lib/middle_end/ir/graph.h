/* graph.h - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H
#define WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H

#include <stdint.h>
#include <stdbool.h>

struct ir_node;
struct ir_func_decl;

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
// void ir_link(struct ir_node *ir);

/// Set a dominator tree of each given function in IR.
///
/// This function traverse function statements and set
/// struct ir_node->idom pointer. It is pointing to immediate
/// dominator, through which we can achieve dominator tree.
///
/// To view dominator tree, ir_dump_dom_tree() should be used.
void ir_compute_dom_tree(struct ir_node *decl);

/// Judge of \p node is dominated by \p dom.
bool ir_dominated_by(struct ir_node *node, struct ir_node *dom);

/// Judge if \p dom is dominator of \p node.
bool ir_dominates(struct ir_node *dom, struct ir_node *node);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H