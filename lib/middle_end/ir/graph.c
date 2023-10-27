/* graph.c - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/graph.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_ops.h"
#include "util/compiler.h"
#include "util/hashmap.h"
#include <assert.h>

static void control_flow_successors(
    struct ir_node *ir,
    struct ir_node **out_main,
    struct ir_node **out_alt
) {
    switch (ir->type) {
    case IR_COND: {
        struct ir_cond *cond = ir->ir;
        *out_main = cond->target;
        *out_alt = ir->next_else;
        break;
    }
    case IR_JUMP: {
        struct ir_jump *jmp = ir->ir;
        *out_main = jmp->target;
        *out_alt = NULL;
        break;
    }
    default: {
        *out_main = ir->next;
        *out_alt = NULL;
        break;
    }
    }
}

__weak_really_inline static void set_idom(
    struct ir_node  *node,
    struct ir_node  *idom,
    struct ir_node **worklist,
    uint64_t        *siz
) {
    if (node->idom == NULL) {
        node->idom = idom;
        if (idom->idom_back[0] == NULL)
            idom->idom_back[0] = node;
        else
            idom->idom_back[1] = node;
        worklist[(*siz)++] = node;
    }
}

/* https://www.cs.utexas.edu/users/misra/Lengauer+Tarjan.pdf
   https://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/a%20fast%20algorithm%20for%20finding.pdf */
static void dominator_tree(struct ir_func_decl *decl)
{
    struct ir_node *root           = decl->body;
    struct ir_node *worklist[2048] = {0};
    uint64_t        siz            =  0;

    root->idom = root;

    worklist[siz++] = root;

    while (siz > 0) {
        struct ir_node *cur = worklist[--siz];

        struct ir_node *succs[2] = {0};
        control_flow_successors(cur, &succs[0], &succs[1]);

        if (succs[0])
            set_idom(succs[0], cur, worklist, &siz);

        if (succs[1])
            set_idom(succs[1], cur, worklist, &siz);
    }
}

static void dominance_frontier(struct ir_node *x)
{
    if (x->idom_back[0])
        dominance_frontier(x->idom_back[0]);

    if (x->idom_back[1])
        dominance_frontier(x->idom_back[1]);

    struct ir_node *succs[2] = {0};

    control_flow_successors(x, &succs[0], &succs[1]);

    for (uint64_t i = 0; i < 2; ++i) {
        struct ir_node *y = succs[i];
        if (y && y->idom != x)
            x->df[x->df_siz++] = y;
    }

    for (uint64_t i = 0; i < 2; ++i) {
        struct ir_node *z = x->idom_back[i];
        if (z) {
            for (uint64_t j = 0; j < z->df_siz; ++j) {
                struct ir_node *y = z->df[j];
                if (y && y->idom != x)
                    x->df[x->df_siz++] = y;
            }
        }
    }
}



static void assigns_collect(struct ir_func_decl *decl, hashmap_t *out)
{
    struct ir_node *it = decl->body;

    while (it) {
        if (it->type == IR_STORE) {
            struct ir_store *store = it->ir;
            assert(store->idx->type == IR_SYM);
            struct ir_sym *sym = store->idx->ir;

            bool ok = 0;
            uint64_t addr = hashmap_get(out, sym->idx, &ok);

            if (!ok) {
                ir_vector_t *assign_list = weak_calloc(1, sizeof (ir_vector_t));
                vector_push_back(*assign_list, it);
                hashmap_put(out, sym->idx, (uint64_t) assign_list);
            } else {
                ir_vector_t *assign_list = (ir_vector_t *) addr;
                vector_push_back(*assign_list, it);
            }
        }

        it = it->next;
    }
}

static void assigns_dump(hashmap_t *assigns)
{
    hashmap_foreach(assigns, k, v) {
        ir_vector_t *list = (ir_vector_t *) v;
        printf("For symbol %ld { ", k);
        vector_foreach(*list, i) {
            printf("%d ", vector_at(*list, i)->instr_idx);
        }
        printf("}\n");
    }
}

/* This function implements algorithm given in
   https://c9x.me/compile/bib/ssa.pdf */
static void phi_insert(struct ir_func_decl *decl)
{
    /* Key:   ir
       Value: 1 | 0 */
    hashmap_t       dom_fron_plus = {0};
    /* Key:   sym_idx
       Value: array of ir's */
    hashmap_t       assigns       = {0};
    /* Key:   ir
       Value: sym_idx */
    hashmap_t       work          = {0};
    ir_vector_t     w             = {0};

    hashmap_init(&assigns, 256);
    hashmap_init(&work, 256);
    hashmap_init(&dom_fron_plus, 256);

    assigns_collect(decl, &assigns);
    assigns_dump(&assigns);

    hashmap_foreach(&assigns, sym_idx, __list) {
        ir_vector_t *assign_list = (ir_vector_t *) __list;

        vector_foreach(*assign_list, i) {
            struct ir_node *x = vector_at(*assign_list, i);

            hashmap_put(&work, (uint64_t) x, 1);
            vector_push_back(w, x);
        }

        while (w.count > 0) {
            struct ir_node *x = vector_back(w);
            vector_pop_back(w);

            for (uint64_t i = 0; i < x->df_siz; ++i) {
                struct ir_node *y = x->df[i];

                bool ok = 0;
                hashmap_get(&dom_fron_plus, (uint64_t) y, &ok);

                if (!ok) {
                    /* TODO: Phi instruction
                       TODO: Which basic block numbers to put into Phi instruction?
                       NOTE: Phi instruction typically has at most two operands. */
                    printf("Should put phi for symbol %ld before instr %d, CFG's = {", sym_idx, y->instr_idx);
                    /* TODO: Control flow predecessors. */
                    printf("%d, %d", y->prev->instr_idx, y->prev_else->instr_idx);
                    puts("}");

                    hashmap_put(&dom_fron_plus, (uint64_t) y, 1);

                    hashmap_get(&work, (uint64_t) y, &ok);
                    if (!ok) {
                        hashmap_put(&work, (uint64_t) y, 1);
                        vector_push_back(w, y);
                    }
                }
            }
        }
    }

    vector_free(w);
    hashmap_destroy(&work);
    hashmap_foreach(&assigns, k, v) {
        (void) k;
        ir_vector_t *assign_list = (ir_vector_t *) v;
        vector_free(*assign_list);
    }
    hashmap_destroy(&assigns);
    hashmap_destroy(&dom_fron_plus);
}



void ir_compute_dom_tree(struct ir_node *ir)
{
    struct ir_node *it = ir;
    while (it) {
        dominator_tree(it->ir);
        it = it->next;
    }
}

void ir_compute_dom_frontier(struct ir_node *decls)
{
    struct ir_node *it = decls;
    while (it) {
        struct ir_func_decl *decl = it->ir;
        dominance_frontier(decl->body);
        it = it->next;
    }
}

void ir_compute_ssa(struct ir_node *decls)
{
    struct ir_node *it = decls;
    while (it) {
        struct ir_func_decl *decl = it->ir;
        phi_insert(decl);
        it = it->next;
    }
}



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