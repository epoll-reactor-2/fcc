/* dom.c - Related to dominator tree routines.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/dom.h"
#include "middle_end/ir/ir.h"
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