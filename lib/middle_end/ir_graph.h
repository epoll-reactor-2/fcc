/* ir_graph.h - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H
#define WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H

#include <stddef.h>
#include <stdbool.h>

/// \todo: How to represent graph?
///     form:  Adjacency matrix
///     usage: SSA form computing using this algorithm:
///            https://www.sciencedirect.com/science/article/pii/S1571066107005324

/// Graph represented as adjacency matrix.
typedef struct {
    /// Tells size N x N of the adjacency matrix.
    size_t  bytes_size;
    /// Always equal sqrt(bytes_size) since
    /// adjacency matrix is square by definition.
    size_t  cols_count;

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
    bool   *adj_matrix;
} ir_graph_t;

typedef struct ir_node_t ir_node_t;

/// Build directed graph from IR statements list.
///
/// \note User should cleanup returnd graph with ir_graph_cleanup().
ir_graph_t ir_graph_init(ir_node_t *ir, size_t ir_size);
void       ir_graph_cleanup(ir_graph_t *g);

#endif // WEAK_COMPILER_MIDDLE_END_IR_GRAPH_H