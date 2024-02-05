/* ssa.c - Static single assignment routines.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ssa.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/gen.h"
#include "middle_end/ir/ir_ops.h"
#include "util/compiler.h"
#include "util/hashmap.h"
#include <assert.h>
#include <math.h>
#include <string.h>



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

static uint64_t dfs_index;

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

    dfs_index = 0;
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

/* Topological sort. */
void dfs(uint64_t u)
{
    visit_time[u] = ++dfs_index;
    inverse_visit_time[dfs_index] = u;

    vector_foreach(graph[u], i) {
        uint64_t v = vector_at(graph[u], i);
        if (!visit_time[v]) {
            dfs(v);
            parent_in_dfs_tree[visit_time[v]] = visit_time[u];
        }
    }
}

/* https://www.cs.princeton.edu/courses/archive/fall03/cs528/handouts/a%20fast%20algorithm%20for%20finding.pdf
   https://baziotis.cs.illinois.edu/compilers/semidominators-proof.html
   https://www.cs.utexas.edu/users/misra/Lengauer+Tarjan.pdf

    The union find and path compression techniques are used
    to speed up algorithm.

    If v < u then v visited before u.
    If v < u then v is ancestor of u in DFS tree. */
void dom_tree()
{
    /* Step 1 already executed by performing DFS. */

    /* Each node dominates itself. */
    for (uint64_t i = 1; i <= dfs_index; ++i) {
        semidom         [i] = i;
        idom            [i] = i;
        union_find      [i] = i;
        path_compression[i] = i;
    }

    /* Traverse results of topological sort in reverse order. */
    for (uint64_t u = dfs_index; u >= 1; --u) {

        /* Step 2: Compute semidominators by applying

                   sdom(w) = min({
                                       v | (v, w) in E && v < w 
                                 } U {
                                       sdom(u) | u > w && E edge (v, w)
                                       such as there is path from u to v
                                 }) */
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

        /* Step 3: Define the immediate dominators. */
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

            /* if (v == 0)
                continue; */

            if (parent_in_dfs_tree[v] == u)
                union_find[v] = u;
        }
    }

    /* Step 4: ??? */
    for (uint64_t i = 1; i <= dfs_index; ++i)
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

        vector_foreach(it->cfg.succs, i) {
            uint64_t u = it->instr_idx;
            uint64_t v = vector_at(it->cfg.succs, i)->instr_idx;

            vector_push_back(graph[u], v);
            vector_push_back(reverse_graph[v], u);
        }

        it = it->next;
        ++cnt;
    }

    return cnt;
}

void ir_dominator_tree(struct ir_fn_decl *decl)
{
    struct ir_node *it                  = decl->body;
    struct ir_node *stmts[MAX_VERTICES] = {0};

    dom_tree_reset_state();

    uint64_t stmts_cnt = dom_tree_fill(it, stmts);

    dfs(0);
    dom_tree();

    for (uint64_t i = 0; i < stmts_cnt; ++i) {
        uint64_t        idom_idx = inverse_visit_time[idom[visit_time[i]]];
        struct ir_node *stmt     = stmts[i];
        struct ir_node *dom      = stmts[idom_idx];

        stmt->idom = dom;
        vector_push_back(dom->idom_back, stmt);
    }
}

/* Cooper algorithm
   https://www.cs.tufts.edu/comp/150FP/archive/keith-cooper/dom14.pdf */
void ir_dominance_frontier(struct ir_fn_decl *decl)
{
    struct ir_node *b = decl->body;

    while (b) {
        if (b->cfg.preds.count >= 2) {
            vector_foreach(b->cfg.preds, pred_i) {
                struct ir_node *p = vector_at(b->cfg.preds, pred_i);
                struct ir_node *runner = p;

                while (runner != b->idom) {
                    vector_push_back(runner->df, b);

                    /* Upper statement is reached. */
                    if (runner == runner->idom)
                        break;

                    runner = runner->idom;
                }
            }
        }

        b = b->next;
    }
}

static void assigns_collect(struct ir_fn_decl *decl, hashmap_t *out)
{
    struct ir_node *it = decl->body;

    hashmap_reset(out, 256);

    while (it) {
        if (it->type == IR_STORE) {
            struct ir_store *store = it->ir;
            assert(store->idx->type == IR_SYM);
            struct ir_sym *sym = store->idx->ir;

            bool ok = 0;
            uint64_t addr = hashmap_get(out, sym->idx, &ok);

            /* Allocate new array on heap and map it like so
               sym_idx -> { assign_1, assign_2, ...} */
            ir_vector_t *list = ok
                ? (ir_vector_t *) addr
                : weak_calloc(1, sizeof (ir_vector_t));

            vector_push_back(*list, it);

            if (!ok)
                hashmap_put(out, sym->idx, (uint64_t) list);
        }

        it = it->next;
    }
}

static void assigns_destroy(hashmap_t *assigns)
{
    hashmap_foreach(assigns, k, v) {
        (void) k;
        vector_free(*(ir_vector_t *) v);
    }
    hashmap_destroy(assigns);
}

/*  TODO: update all links correctly (IR list and CFG).

    (prev    ) -- next --> (curr    )
    (prev    ) <- prev --- (curr    )

    (prev    ) -- next --> (new     ) -- next --> (curr    )
    (prev    ) <- prev --- (new     ) <- prev --- (curr    ) */
static void ir_insert_before(struct ir_node *curr, struct ir_node *new)
{
    struct ir_node *prev = curr->prev;

    prev->next = new;
    new->prev = prev;
    new->next = curr;
    curr->prev = new;

    vector_push_back(prev->cfg.succs, new);
    vector_push_back(curr->cfg.preds, new);

    /* TODO: Now first SSA renaming algorithm visits
             statement after phi, then before. Fix it
             by introducing correct predecessors.
             Phi node must be the only predecessor of next statement. */

    /* To traverse dominator tree next. */
    vector_push_back(curr->idom_back, new);
}

/* This function implements algorithm given in
   https://c9x.me/compile/bib/ssa.pdf */
static void phi_insert(
    struct ir_fn_decl *decl,
    /* Key:   sym_idx
       Value: array of ir's */
    hashmap_t *assigns
) {
    /* Key:   ir
       Value: 1 | 0 */
    hashmap_t       dom_fron_plus = {0};
    /* Key:   ir
       Value: sym_idx */
    hashmap_t       work          = {0};
    ir_vector_t     w             = {0};

    hashmap_foreach(assigns, sym_idx, __list) {
        hashmap_reset(&dom_fron_plus, 256);
        hashmap_reset(&work, 256);
        /* `w` vector generally can be left uncleared, since algorithm
           assumes that we do something while it not empty. So now it
           guaranteed to be empty. */

        ir_vector_t *assign_list = (ir_vector_t *) __list;

        vector_foreach(*assign_list, i) {
            (void) i;
            hashmap_put(&work, 0, 0);
        }

        struct ir_node *it = decl->body;
        while (it) {
            hashmap_put(&dom_fron_plus, (uint64_t) it, 0);
            it = it->next;
        }

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

                bool ok = 0;
                uint64_t got = hashmap_get(&dom_fron_plus, y_addr, &ok);
                if (ok && got == 0) {
                    struct ir_node *phi = ir_phi_init(
                        sym_idx,
                        y->instr_idx,
                        vector_at(y->cfg.preds, 0)->instr_idx
                    );

                    ir_insert_before(y, phi);
                    /* printf("Insert phi before %ld\n", y->instr_idx); */
                    memcpy(&phi->meta, &y->meta, sizeof (struct meta));
                    hashmap_put(&dom_fron_plus, y_addr, 1);

                    ok = 0;
                    uint64_t val = hashmap_get(&work, y_addr, &ok);
                    if (ok && val == 0) {
                        hashmap_put(&work, (uint64_t) y, 1);
                        vector_push_back(w, y);
                    }
                }
            }
        }
    }

    vector_free(w);
    hashmap_destroy(&work);
    hashmap_destroy(&dom_fron_plus);
}

typedef vector_t(uint64_t) ssa_stack_t;

static uint64_t ssa_idx;

really_inline static void ssa_rename_sym(struct ir_node *sym_ir, uint64_t sym_idx, ssa_stack_t *stack)
{
    if (sym_ir->type != IR_SYM)
        return;

    struct ir_sym *sym = sym_ir->ir;
    if (sym->idx == sym_idx)
        sym->ssa_idx = vector_back(*stack);
}

static void ssa_rename_bin(struct ir_bin *bin, uint64_t sym_idx, ssa_stack_t *stack)
{
    ssa_rename_sym(bin->lhs, sym_idx, stack);
    ssa_rename_sym(bin->rhs, sym_idx, stack);
}

static void ssa_rename(struct ir_node *ir, uint64_t sym_idx, ssa_stack_t *stack, bool *visited)
{
    if (visited[ir->instr_idx])
        return;

    visited[ir->instr_idx] = 1;

    switch (ir->type) {
    case IR_PHI: {
        struct ir_phi *phi = ir->ir;
        if (phi->sym_idx == sym_idx) {
            phi->ssa_idx = ssa_idx;
            vector_push_back(*stack, ssa_idx++);
        }
        break;
    }
    case IR_COND: {
        struct ir_cond *cond = ir->ir;
        struct ir_bin  *body = cond->cond->ir;

        ssa_rename_bin(body, sym_idx, stack);
        break;
    }
    case IR_STORE: {
        struct ir_store *store = ir->ir;
        if (store->idx->type == IR_SYM) {
            struct ir_sym *sym = store->idx->ir;
            if (sym->idx == sym_idx) {
                sym->ssa_idx = ssa_idx;
                vector_push_back(*stack, ssa_idx++);
            }
        }

        switch (store->body->type) {
        case IR_BIN: {
            struct ir_bin *body = store->body->ir;
            ssa_rename_bin(body, sym_idx, stack);
            break;
        }
        case IR_SYM: {
            ssa_rename_sym(store->body, sym_idx, stack);
            break;
        }
        default:
            break;
        }
        break;
    }
    case IR_RET: {
        struct ir_ret *ret = ir->ir;
        if (ret->body &&
            ret->body->type == IR_SYM)
            ssa_rename_sym(ret->body, sym_idx, stack);
    }
    default:
        break;
    }

    /* 1. Some logic with phi nodes. */
    vector_foreach(ir->cfg.succs, i) {
        struct ir_node *it = vector_at(ir->cfg.succs, i);
        if (it->type == IR_PHI) {
            /* ... */
            struct ir_phi *phi = it->ir;
            if (phi->sym_idx == sym_idx &&
                stack->count > 0) {
                /* TODO: Store variable list assigned in
                         each related block in phi node.
                         Then rename operands of phi. */
                phi->ssa_idx = vector_back(*stack);
            }
        }
    }

    /* 2. call recursive for dominator tree children. */
    vector_foreach(ir->idom_back, i) {
        struct ir_node *submissive = vector_at(ir->idom_back, i);
        ssa_rename(submissive, sym_idx, stack, visited);
    }

    /* 3. Pop from stack for current assignment. */
    if (ir->type == IR_STORE) {
        struct ir_store *store = ir->ir;
        if (store->idx->type != IR_SYM)
            return;
        struct ir_sym *sym = store->idx->ir;
        if (sym->idx == sym_idx)
            vector_pop_back(*stack);
    }
}

void ir_compute_ssa(struct ir_node *decls)
{
    struct ir_node *it = decls;
    while (it) {
        struct ir_fn_decl *decl = it->ir;
        /* Key:   sym_idx
           Value: array of ir's */
        hashmap_t assigns        = {0};
        /* Value: sym_idx */
        ssa_stack_t ssa_stack    = {0};

        assigns_collect(decl, &assigns);

        dom_tree_reset_state();
        ir_dominator_tree(decl);
        ir_dominance_frontier(decl);
        phi_insert(decl, &assigns);
        ir_cfg_build(decl);

        hashmap_foreach(&assigns, sym_idx, __) {
            bool visited[512] = {0};

            (void) __;
            vector_free(ssa_stack);
            ssa_idx = 0;
            ssa_rename(decl->body, sym_idx, &ssa_stack, visited);
        }

        it = it->next;

        assigns_destroy(&assigns);
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
Вновь кружатся осадки
Я в метели ищу силуэт
На плечах незашитый ватник
На снегу запорошенный след

На забытом Богом участке
В маленьком поле в лесу
Я узрел твой облик прекрасный

Я оставлю калитку открытой
Ты прости за косой забор
И тазы под текущей крышей
Я давно запустил этот дом

Пол скрипит от шагов одиноких
И чтобы дым мимо не проходил
Все отворены створки

Лишь для тебя в холодах января
Мои двери и окна распахнуты настежь
Лишь для тебя, погибель моя
Моё старое сердце распахнуто настежь
*/