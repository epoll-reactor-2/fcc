/* ssa.h - Static single assignment routines.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_SSA_H
#define WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H

#include <stdint.h>
#include <stdbool.h>

struct ir_node;
struct ir_func_decl;

/// Set a dominator tree of each given function in IR.
///
/// This function traverse function statements and set
/// struct ir_node->idom pointer. It is pointing to immediate
/// dominator, through which we can achieve dominator tree.
///
/// To view dominator tree, ir_dump_dom_tree() should be used.
void ir_compute_dom_tree(struct ir_node *decls);

void ir_compute_dom_frontier(struct ir_node *decls);

void ir_compute_ssa(struct ir_node *decls);

/// Judge of \p node is dominated by \p dom.
bool ir_dominated_by(struct ir_node *node, struct ir_node *dom);

/// Judge if \p dom is dominator of \p node.
bool ir_dominates(struct ir_node *dom, struct ir_node *node);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H