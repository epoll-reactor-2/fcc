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
#include <math.h>

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



#define MAX_VERTICES 512

#define MIN(a,b) (((a)<(b))?(a):(b))

static vector_t(int) graph        [MAX_VERTICES];
static vector_t(int) reverse_graph[MAX_VERTICES];
/* semidoms[u] = {v | sdom[v] = u} */
static vector_t(int) semidoms     [MAX_VERTICES];

static uint64_t visit_time        [MAX_VERTICES];
static uint64_t inverse_visit_time[MAX_VERTICES];
static uint64_t parent_in_dfs_tree[MAX_VERTICES];
static uint64_t semidom           [MAX_VERTICES];
static uint64_t idom              [MAX_VERTICES];
static uint64_t union_find        [MAX_VERTICES];
static uint64_t path_compression  [MAX_VERTICES];

static uint64_t current_time;

static void dom_tree_reset_state()
{
    for (uint64_t i = 0; i < MAX_VERTICES; ++i) {
        vector_free(graph[i]);
        vector_free(reverse_graph[i]);
        vector_free(semidoms[i]);
    }

    memset(graph,              0, sizeof (graph));
    memset(reverse_graph,      0, sizeof (reverse_graph));
    memset(semidoms,           0, sizeof (semidoms));
    memset(visit_time,         0, sizeof (visit_time));
    memset(inverse_visit_time, 0, sizeof (inverse_visit_time));
    memset(parent_in_dfs_tree, 0, sizeof (parent_in_dfs_tree));
    memset(semidom,            0, sizeof (semidom));
    memset(idom,               0, sizeof (idom));
    memset(union_find,         0, sizeof (union_find));
    memset(path_compression,   0, sizeof (path_compression));

    current_time = 0;
}

struct edge {
    uint64_t from;
    uint64_t to;
};

struct edge least_semidom(uint64_t u)
{
    if (u == union_find[u]) {
        struct edge e = {
            .from = u,
            .to   = u
        };
        return e;
    }

    struct edge got = least_semidom(union_find[u]);
    uint64_t p      = got.from;
    union_find[u]   = got.to;

    if (semidom[p] < semidom[path_compression[u]])
        path_compression[u] = p;

    struct edge e = {
        .from = path_compression[u],
        .to   = union_find[u]
    };

    return e;
}

void dfs(uint64_t u)
{
    visit_time[u] = ++current_time;
    inverse_visit_time[current_time] = u;
    vector_foreach(graph[u], i) {
        uint64_t v = vector_at(graph[u], i);
        if (!visit_time[v]) {
            dfs(v);
            parent_in_dfs_tree[visit_time[v]] = visit_time[u];
        }
    }
}

void dom_tree()
{
    for (uint64_t i = 1; i <= current_time; ++i) {
        semidom         [i] = i;
        idom            [i] = i;
        union_find      [i] = i;
        path_compression[i] = i;
    }

    for (uint64_t u = current_time; u >= 1; --u) {
        vector_foreach(reverse_graph[inverse_visit_time[u]], i) {
            uint64_t v = vector_at(reverse_graph[inverse_visit_time[u]], i);
            v = visit_time[v];

            /* if (v == 0)
                continue; */

            if (v < u)
                semidom[u] = MIN(semidom[u], semidom[v]);
            else
                semidom[u] = MIN(semidom[u], semidom[least_semidom(v).from]);
        }
        vector_push_back(semidoms[semidom[u]], u);

        vector_foreach(semidoms[u], i) {
            uint64_t v    = vector_at(semidoms[u], i);
            uint64_t best = least_semidom(v).from;

            if (semidom[best] >= u)
                idom[v] = u;
            else
                idom[v] = best;
        }

        vector_foreach(graph[inverse_visit_time[u]], i) {
            uint64_t v = vector_at(graph[inverse_visit_time[u]], i);
            v = visit_time[v];

            if (v == 0)
                continue;

            if (parent_in_dfs_tree[v] == u)
                union_find[v] = u;
        }
    }

    for (uint64_t i = 1; i <= current_time; ++i)
        if (idom[i] != semidom[i])
            idom[i]  = idom[idom[i]];
}

/* Put IR nodes to static array. Used in this specific dominator
   tree algorithm.

   Returns number of added items. */
static uint64_t dom_tree_fill(struct ir_node *it, struct ir_node **stmts)
{
    uint64_t cnt = 0;

    while (it) {
        stmts[it->instr_idx] = it;

        struct ir_node *succs[2] = {0};
        control_flow_successors(it, &succs[0], &succs[1]);

        for (uint64_t i = 0; i < 2; ++i)
            if (succs[i]) {
                uint64_t u = it->instr_idx;
                uint64_t v = succs[i]->instr_idx;

                vector_push_back(graph[u], v);
                vector_push_back(reverse_graph[v], u);
            }

        it = it->next;
        ++cnt;
    }

    return cnt;
}

void ir_dominator_tree(struct ir_func_decl *decl)
{
    struct ir_node *it                  = decl->body;
    struct ir_node *stmts[MAX_VERTICES] = {0};

    dom_tree_reset_state();

    uint64_t stmts_cnt = dom_tree_fill(it, stmts);

    dfs(0);
    dom_tree();

    for (uint64_t i = 0; i < stmts_cnt; ++i) {
        uint64_t idom_idx = inverse_visit_time[idom[visit_time[i]]];
        stmts[i]->idom = stmts[idom_idx];
    }
}

/* Cooper algorithm
   https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf */
static void dominance_frontier(struct ir_node *ir)
{
    struct ir_node *b = ir;

    while (b) {
        vector_free(b->df);
        ir_vector_t preds = {0};
        if (b->prev)      vector_push_back(preds, b->prev);
        if (b->prev_else) vector_push_back(preds, b->prev_else);

        if (preds.count >= 2) {
            printf("DF for %ld\n", b->instr_idx);
            vector_foreach(preds, pred_i) {
                struct ir_node *p = vector_at(preds, pred_i);
                struct ir_node *runner = p;

                while (runner != runner->idom && runner != b->idom) {
                    vector_push_back(runner->df, b);
                    runner = runner->idom;
                }
            }
        }

        b = b->next;
        vector_free(preds);
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
            printf("%ld ", vector_at(*list, i)->instr_idx);
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
            uint64_t x_addr = (uint64_t) x;

            hashmap_put(&work, x_addr, 1);
            vector_push_back(w, x);
        }

        while (w.count > 0) {
            struct ir_node *x = vector_back(w);
            vector_pop_back(w);

            vector_foreach(x->df, i) {
                struct ir_node *y = vector_at(x->df, i);
                uint64_t y_addr = (uint64_t) y;

                if (!hashmap_has(&dom_fron_plus, y_addr)) {
                    /* NOTE: prev & prev_else are control flow (not just list) predecessors.
                             and they are built during IR linkage. */
                    struct ir_node *phi = ir_phi_init(sym_idx, y->prev->instr_idx, y->prev_else->instr_idx);
                    printf("insert phi(%ld) before %%%ld\n", sym_idx, y->instr_idx);
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
        dom_tree_reset_state();
        ir_dominator_tree(decl);
        puts("");
        dominance_frontier(decl->body);
        phi_insert(decl);
        it = it->next;
    }
}



bool ir_dominated_by(struct ir_node *node, struct ir_node *dom)
{
    if (node == dom) return 1;

    while (node && node != node->idom) {
        node = node->idom;
        if (node == dom) return 1;
    }
    return 0;
}

bool ir_dominates(struct ir_node *dom, struct ir_node *node)
{
    if (dom == node) return 1;

    while (node && node != node->idom) {
        node = node->idom;
        if (node && node == dom) return 1;
    }
    return 0;
}

/*
Steck' ein Messer in mein Bein und es kommt Blut raus
Doch die Schmerzen gehen vorbei
Meine Schwestern schreiben: „Bro, du siehst nicht gut aus“
Kann schon sein, weil ich bin high
*/