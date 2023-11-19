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
struct ir_fn_decl;

void ir_dominator_tree(struct ir_fn_decl *decl);

void ir_dominance_frontier(struct ir_fn_decl *decl);

void ir_compute_ssa(struct ir_node *functions);

/** Judge of \p node is dominated by \p dom. */
bool ir_dominated_by(struct ir_node *node, struct ir_node *dom);

/** Judge if \p dom is dominator of \p node. */
bool ir_dominates(struct ir_node *dom, struct ir_node *node);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H