/* ir_graph.c - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_graph.h"
#include "middle_end/ir.h"
#include "utility/alloc.h"
#include "utility/compiler.h"

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

    for (uint64_t i = 0; i < ir_size; ++i)
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

    return graph;
}

void ir_graph_cleanup(struct ir_graph *g)
{
    weak_free(g->adj_matrix);
}