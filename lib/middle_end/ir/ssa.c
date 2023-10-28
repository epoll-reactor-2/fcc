/* ssa.c - Static single assignment routines.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ssa.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_ops.h"
#include "util/compiler.h"
#include "util/hashmap.h"
#include <assert.h>
#include <string.h>


static void reset_hashmap(hashmap_t *map, uint64_t siz)
{
    if (map->buckets) {
        hashmap_destroy(map);
    }
    hashmap_init(map, siz);
}



static void control_flow_successors(
    struct ir_node *ir,
    struct ir_node **out_main,
    struct ir_node **out_alt
) {
    switch (ir->type) {
    case IR_COND: {
        struct ir_cond *cond = ir->ir;
#if 1
        *out_main = cond->target;
        *out_alt = ir->next_else;
#else
        *out_main = ir->next_else;
        *out_alt = cond->target;
#endif
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
        vector_push_back(idom->idom_back, node);
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

static void traverse_cfg_post_order(ir_vector_t *out, struct ir_node *ir)
{
    vector_foreach(ir->idom_back, i) {
        struct ir_node *x = vector_at(ir->idom_back, i);
        if (x)
            traverse_cfg_post_order(out, x);
    }
    vector_push_back(*out, ir);
}

/* This function implements algorithm given in
   https://c9x.me/compile/bib/ssa.pdf */
static void dominance_frontier(struct ir_node *ir)
{
    ir_vector_t post_order = {0};
    traverse_cfg_post_order(&post_order, ir);

    vector_foreach(post_order, i) {
        struct ir_node *x = vector_at(post_order, i);
        vector_free(x->df);

        /* printf("Post order: %d, idom = %d, idom_back = ( ", x->instr_idx, x->idom->instr_idx);
        vector_foreach(x->idom_back, j) {
            struct ir_node *z = vector_at(x->idom_back, j);
            printf("%d ", z->instr_idx);
        }
        printf("), CFG succs = ( "); */

        struct ir_node *succs[2] = {0};
        control_flow_successors(x, &succs[0], &succs[1]);

        /* for (uint64_t j = 0; j < 2; ++j) {
            struct ir_node *y = succs[j];
            if (y)
                printf("%d ", y->instr_idx);
        }
        puts(")"); */

        for (uint64_t j = 0; j < 2; ++j) {
            struct ir_node *y = succs[j];
            if (y && y->idom != x) {
                /* printf("1: Add %d to DF(%d)\n", y->instr_idx, x->instr_idx); */
                vector_push_back(x->df, y);
            }
        }

        vector_foreach(x->idom_back, j) {
            struct ir_node *z = vector_at(x->idom_back, j);
            vector_foreach(z->df, k) {
                struct ir_node *y = vector_at(z->df, k);
                if (y && y->idom != x) {
                    /* printf("2: Add %d to DF(%d)\n", y->instr_idx, x->instr_idx); */
                    vector_push_back(x->df, y);
                }
            }
        }
    }

    vector_free(post_order);
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

/*
    (prev    ) -- next --> (  ir    )
    (prev    ) <- prev --- (  ir    )

    (prev    ) -- next --> (new node) -- next --> (  ir    )
    (prev    ) <- prev --- (new node) <- prev --- (  ir    )
*/
static void ir_insert_before(struct ir_node *ir, struct ir_node *new)
{
    struct ir_node *prev = ir->prev;

    prev->next = new;
    new->prev = prev;
    new->next = ir;
    ir->prev = new;
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

    reset_hashmap(&assigns, 256);
    assigns_collect(decl, &assigns);
    assigns_dump(&assigns);

    hashmap_foreach(&assigns, sym_idx, __list) {
        reset_hashmap(&dom_fron_plus, 256);
        reset_hashmap(&work, 256);
        vector_free(w);

        printf("Analyze %ld, ", sym_idx);

        ir_vector_t *assign_list = (ir_vector_t *) __list;

        vector_foreach(*assign_list, i) {
            struct ir_node *x = vector_at(*assign_list, i);

            hashmap_put(&work, (uint64_t) x, 1);
            vector_push_back(w, x);
        }

        while (w.count > 0) {
            struct ir_node *x = vector_back(w);
            vector_pop_back(w);

            vector_foreach(x->df, i) {
                struct ir_node *y = vector_at(x->df, i);
                uint64_t y_addr = (uint64_t) y;

                if (!hashmap_has(&dom_fron_plus, y_addr)) {
                    /* NOTE: prev & prev_else are control flow (not just list list) predecessors.
                             and they are built during IR linkage. */
                    struct ir_node *phi = ir_phi_init(sym_idx, y->prev->instr_idx, y->prev_else->instr_idx);
                    printf("insert phi before %%%d\n", y->instr_idx);
                    ir_insert_before(y, phi);
                    memcpy(&phi->meta, &y->meta, sizeof (struct meta));

                    hashmap_put(&dom_fron_plus, (uint64_t) y, 1);

                    if (!hashmap_has(&work, y_addr)) {
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
        vector_free(*(ir_vector_t *) v);
    }
    hashmap_destroy(&assigns);
    hashmap_destroy(&dom_fron_plus);
}

void ir_compute_ssa(struct ir_node *decls)
{
    struct ir_node *it = decls;
    while (it) {
        struct ir_func_decl *decl = it->ir;
        dominator_tree(decl);
        puts("");
        dominance_frontier(decl->body);
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