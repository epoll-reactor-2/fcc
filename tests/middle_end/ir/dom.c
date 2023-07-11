/* dom.c - Tests for IR dominator properties.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/ir/graph.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void dominates()
{
    TEST_START_INFO

    struct ir_node *node1 = ir_jump_init(0);
    struct ir_node *node2 = ir_jump_init(1);

    /// Dominator tree:
    ///
    ///     +-------+
    ///     |   1   |
    ///     +-------+
    ///         |
    ///         | Dominates
    ///         V
    ///     +-------+
    ///     |   2   |
    ///     +-------+
    node1->idom = NULL;
    node2->idom = node1;

    ASSERT_TRUE( ir_dominates   (node1, node2));
    ASSERT_TRUE(!ir_dominated_by(node1, node2));

    ASSERT_TRUE(!ir_dominates   (node2, node1));
    ASSERT_TRUE( ir_dominated_by(node2, node1));

    ir_node_cleanup(node1);
    ir_node_cleanup(node2);

    TEST_END_INFO
}

int main()
{
    dominates();
}