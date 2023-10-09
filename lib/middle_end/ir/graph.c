
/* graph.c - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/graph.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ir.h"
#include "util/compiler.h"

__weak_really_inline static void ir_set_idom(
    struct ir_node  *node,
    struct ir_node  *idom,
    struct ir_node **worklist,
    uint64_t        *siz
) {
    /// \todo: Link conditions. Rewrite removed ir_link().
    if (node->idom == NULL) {
        node->idom = idom;
        worklist[(*siz)++] = node;
    }
}

static void ir_dom_tree_func_decl(struct ir_func_decl *decl)
{
    struct ir_node *root           = &decl->body[0];
    struct ir_node *worklist[2048] = {0};
    uint64_t        siz            =  0;

    root->idom = root;

    worklist[siz++] = root;

    /// \todo: Dominance by in-statement variable indices.
    ///        Now immediate dominators are attached to
    ///        the wrong nodes. I guess, correct dom tree
    ///        in general should be "wider" than "taller".
    while (siz > 0) {
        struct ir_node *cur = worklist[--siz];

        switch (cur->type) {
        case IR_IMM:
        case IR_SYM:
        case IR_BIN:
        case IR_MEMBER:
            break;
        case IR_STORE: {
            struct ir_node *succ = cur->next;
            ir_set_idom(succ, cur, worklist, &siz);
            break;
        }
        case IR_JUMP: {
            struct ir_jump *jump = cur->ir;
            struct ir_node *succ = jump->target;
            ir_set_idom(succ, cur, worklist, &siz);
            break;
        }
        case IR_COND: {
            struct ir_cond *cond  = cur->ir;
            struct ir_node *succ1 = cond->target;
            struct ir_node *succ2 = cur->next_else;
            ir_set_idom(succ1, cur, worklist, &siz);
            ir_set_idom(succ2, cur, worklist, &siz);
            break;
        }
        case IR_RET:
        case IR_RET_VOID: {
            struct ir_node *succ = cur->next;
            if (succ)
                ir_set_idom(succ, cur, worklist, &siz);
            break;
        }
        case IR_ALLOCA: {
            struct ir_node *succ = cur->next;
            ir_set_idom(succ, cur, worklist, &siz);
            break;
        }
        case IR_FUNC_CALL: {
            struct ir_node *succ = cur->next;
            ir_set_idom(succ, cur, worklist, &siz);
            break;
        }
        default:
            break;
        }
    }
}

#define WEAK_DEBUG_DOMINATOR_TREE 1

#if WEAK_DEBUG_DOMINATOR_TREE == 1
# include <stdio.h>
# include "util/unreachable.h"

void ir_compute_dom_tree(struct ir_node *ir)
{
    FILE *cfg = fopen("/tmp/graph_cfg.dot", "w");
    FILE *dom = fopen("/tmp/graph_dom.dot", "w");
    if (!cfg) weak_unreachable("Open failed");
    if (!dom) weak_unreachable("Open failed");

    struct ir_node *it = ir;
    while (it) {
        ir_dom_tree_func_decl(it->ir);
        /// ir_dump(stdout, it->ir);
        /// ir_dump_graph_dot(cfg, it->ir);
        ir_dump_cfg(cfg, it->ir);
        ir_dump_dom_tree(dom, it->ir);
        it = it->next;
    }

    fclose(dom);
    fclose(cfg);
}
#else /// !WEAK_DEBUG_DOMINATOR_TREE
void ir_compute_dom_tree(struct ir_node *ir)
{
    struct ir_node *it = ir;
    while (it) {
        ir_dom_tree_func_decl(it->ir);
        it = it->next;
    }
}
#endif /// !WEAK_DEBUG_DOMINATOR_TREE

bool ir_dominated_by(struct ir_node *node, struct ir_node *dom)
{
    if (node == dom) return 1;

    while (node) {
        node = node->idom;
        if (node == dom) return 1;
    }
    return 0;
}

bool ir_dominates(struct ir_node *dom, struct ir_node *node)
{
    /// Note:
    /// It is possible to call there ir_is_dominated_by(),
    /// but this function is never inlineable in this context.
    if (dom == node) return 1;

    while (node) {
        node = node->idom;
        if (node == dom) return 1;
    }
    return 0;
}

/*
Steck' ein Messer in mein Bein und es kommt Blut raus
Doch die Schmerzen gehen vorbei
Meine Schwestern schreiben: „Bro, du siehst nicht gut aus“
Kann schon sein, weil ich bin high
*/