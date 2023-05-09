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
    ir_graph_t *graph,
    size_t      col,
    size_t      row,
    bool        v
) {
    graph->adj_matrix[graph->cols_count * col + row] = v;
}

static __weak_unused inline bool ir_graph_get_at(
    ir_graph_t *graph,
    size_t      col,
    size_t      row
) {
    return graph->adj_matrix[graph->cols_count * col + row];
}

static void ir_graph_build_matrix(
    ir_node_t  *ir,
    ir_graph_t *graph
) {
    size_t ir_size = graph->cols_count;

    for (size_t i = 0; i < ir_size; ++i)
        switch (ir[i].type) {
        case IR_COND: {
            ir_cond_t *cond = ir[i].ir;
            /// Make edge to the next statement.
            ir_graph_set_at(graph, i + 1, i, 1);
            /// Make edge to the jump target.
            ir_graph_set_at(graph, cond->goto_label, i, 1);
            break;
        }
        case IR_JUMP: {
            ir_jump_t *jump = ir[i].ir;
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

ir_graph_t ir_graph_init(ir_node_t *ir, size_t ir_size)
{
    size_t matrix_size = ir_size * ir_size;

    ir_graph_t graph = {
        .bytes_size = matrix_size,
        .cols_count = ir_size,
        .adj_matrix = weak_calloc(matrix_size, sizeof (bool))
    };

    ir_graph_build_matrix(ir, &graph);

    return graph;
}

void ir_graph_cleanup(ir_graph_t *g)
{
    weak_free(g->adj_matrix);
}