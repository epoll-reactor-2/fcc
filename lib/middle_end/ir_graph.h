/* ir_graph.h - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H
#define WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H

#include <stdint.h>
#include <stdbool.h>

/// \todo: How to represent graph?
///     form:  Adjacency matrix
///     usage: SSA form computing using this algorithm:
///            https://www.sciencedirect.com/science/article/pii/S1571066107005324

/// Graph represented as adjacency matrix.
struct ir_graph {
    /// Tells size N x N of the adjacency matrix.
    uint64_t bytes_size;
    /// Always equal sqrt(bytes_size) since
    /// adjacency matrix is square by definition.
    uint64_t cols_count;

    /// Example:
    ///          C0   C1    C2
    ///
    /// L0    [   0    1    0   ]
    /// L1    [   0    1    0   ]
    /// L1    [   0    0    1   ]
    ///
    /// Row is vertex.
    /// Column is edge between vertices.
    ///
    /// 1 indicates edge from graph node (L%) to graph node (C%)
    /// 0 indicates edge disconnection
    bool *adj_matrix;
};

struct ir;

/// Build directed graph from IR statements list.
///
/// \todo For now in debug purpose, graph only for first
///       given IR function is built and returned.
///
/// \note User should cleanup returnd graph with ir_graph_cleanup().
struct ir_graph ir_graph_init(struct ir *ir);

void ir_graph_cleanup(struct ir_graph *g);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H