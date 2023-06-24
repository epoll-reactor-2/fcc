/* ir_graph.c - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_graph.h"
#include "middle_end/ir_dump.h"
#include "middle_end/ir.h"
#include "util/alloc.h"
#include "util/compiler.h"
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>

static __weak_unused void ir_graph_dfs(struct ir_graph *graph);
static __weak_unused void ir_graph_build_dom_tree(
    struct ir_graph *graph,
    struct ir_graph *out_dom_tree,
    struct ir_node  *decls
);

static __weak_unused inline void ir_graph_set_at(
    struct ir_graph *graph,
    uint64_t         col,
    uint64_t         row,
    bool             v
) {
    graph->adj_matrix[graph->cols_count * col + row] = v;
}

static __weak_unused inline bool ir_graph_get_at(
    struct ir_graph *graph,
    uint64_t         col,
    uint64_t         row
) {
    return graph->adj_matrix[graph->cols_count * col + row];
}

static void ir_graph_build_matrix(
    struct ir_node  *ir,
    struct ir_graph *graph
) {
    uint64_t ir_size = graph->cols_count;

    /// Last instruction in function is always ret,
    /// so it cannot jump anywhere.
    for (uint64_t i = 0; i < ir_size - 1; ++i)
        switch (ir[i].type) {
        case IR_COND: {
            struct ir_cond *cond = ir[i].ir;
            /// Make edge to the next statement.
            ir_graph_set_at(graph, i + 1, i, 1);
            /// Make edge to the jump target.
            ir_graph_set_at(graph, cond->goto_label, i, 1);
            break;
        }
        case IR_JUMP: {
            struct ir_jump *jump = ir[i].ir;
            /// Make edge only to the jump target, not
            /// to next statement after this one.
            ir_graph_set_at(graph, jump->idx, i, 1);
            break;
        }
        case IR_RET:
        case IR_RET_VOID: {
            /// Do nothing.
            break;
        }
        default: {
            /// All other statements are sequentional ones.
            /// Make edge to the next statement.
            ir_graph_set_at(graph, i + 1, i, 1);
            break;
        }
        } /// switch
}

struct ir_graph ir_graph_init(struct ir *ir)
{
    /// \todo Placeholder. Implement for multiple functions.
    struct ir_func_decl *decl = ir->decls[0].ir;
    uint64_t matrix_size = decl->body_size * decl->body_size;

    struct ir_graph graph = {
        .bytes_size = matrix_size,
        .cols_count = decl->body_size,
        .adj_matrix = weak_calloc(matrix_size, sizeof (bool))
    };

    ir_graph_build_matrix(decl->body, &graph);

    // ir_graph_dfs(&graph);

    struct ir_graph dom_tree = {
        .bytes_size = matrix_size,
        .cols_count = decl->body_size,
        .adj_matrix = weak_calloc(matrix_size, sizeof (bool))
    };

    ir_graph_build_dom_tree(&graph, &dom_tree, ir->decls);

    return graph;
}

void ir_graph_cleanup(struct ir_graph *g)
{
    weak_free(g->adj_matrix);
}

/*******************************************************
 * Playground, for now not related to the compiler.    *
 *                                                     *
 * Just reminder for me what the graph is.             *
 *******************************************************/
static void __ir_graph_dfs(
    struct ir_graph *graph,
    bool            *visited,
    uint64_t         from
);

static void ir_graph_dfs(struct ir_graph *graph)
{
    bool *visited = weak_calloc(graph->bytes_size, sizeof (bool));

    __ir_graph_dfs(graph, visited, 0);

    weak_free(visited);
}

static void __ir_graph_dfs(
    struct ir_graph *graph,
    bool            *visited,
    uint64_t         from
) {
    uint64_t  total = graph->cols_count;
    bool     *matrix = graph->adj_matrix;

    visited[from] = 1;

    for (uint64_t i = 0; i < total; ++i) {
        for (uint64_t j = 0; j < total; ++j) {
            uint64_t idx = i * total + j;
            if (!visited[idx] && matrix[idx]) {
                /// Pre-order traversal.
                printf("\nDFS at %ld:%ld", i, j);

                __ir_graph_dfs(graph, visited, idx);

                /// Post-order traversal.
                /// ...
            }
        }
    }
}

/// \todo: Compute dominance not by node indices, but by
///        variable indices inside each node.
///
///        +--------------+  This should be root of all
///        | store %1, %2 |  nodes, that contain %1 and %2
///        +--------------+
static __weak_unused void ir_graph_build_dom_tree(
    struct ir_graph *graph,
    struct ir_graph *out_dom_tree,
    struct ir_node  *decls
) {
    uint64_t  siz  = graph->cols_count;
     int64_t *doms = weak_calloc(siz, sizeof (int64_t));

    for (uint64_t i = 0; i < siz; ++i) {
        doms[i] = -1; /// Undefined.

        for (uint64_t j = 0; j < siz; ++j) {
            if (ir_graph_get_at(graph, i, j)) {
                if (doms[i] == -1) {
                    doms[i] = j;
                } else {
                    int idom = doms[i];
                    while (idom != doms[idom] && doms[idom] != -1)
                        idom = doms[idom];
                    int intersect = idom;
                    idom = doms[i];
                    while (idom != intersect && idom != -1) {
                        doms[i] = intersect;
                        idom = doms[intersect];
                        while (idom != intersect && idom != -1) {
                            idom = doms[idom];
                        }
                        intersect = idom;
                    }
                }
            }
        }
    }

    for (uint64_t i = 1; i < siz; ++i)
        ir_graph_set_at(out_dom_tree, i, doms[i], 1);

    struct ir_func_decl *func = (struct ir_func_decl *) decls[0].ir;

    FILE *stream_1 = fopen("/tmp/graph_1.dot", "w");
    FILE *stream_2 = fopen("/tmp/graph_2.dot", "w");

    // printf("Dom tree (source):\n");
    ir_dump_graph_dot(stream_1, graph->adj_matrix, func->body_size, func->body);
    // printf("Dom tree (output):\n");
    ir_dump_graph_dot(stream_2, out_dom_tree->adj_matrix, func->body_size, func->body);

    fflush(stream_1);
    fflush(stream_2);
    fclose(stream_1);
    fclose(stream_2);

    weak_free(doms);
}

/*
Steck' ein Messer in mein Bein und es kommt Blut raus
Doch die Schmerzen gehen vorbei
Meine Schwestern schreiben: „Bro, du siehst nicht gut aus“
Kann schon sein, weil ich bin high
*/