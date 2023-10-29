/* dom.c - Tests for IR dominator properties.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ssa.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void dominates()
{
    TEST_START_INFO

    ir_reset_internal_state();

    struct ir_node *_1 = ir_jump_init(0);
    struct ir_node *_2 = ir_jump_init(1);

    /* Dominator tree:

           +-------+
           |   1   |
           +-------+
               |
               | Dominates
               V
           +-------+
           |   2   |
           +-------+ */
    _1->idom = NULL;
    _2->idom = _1;

    ASSERT_TRUE( ir_dominates   (_1, _2));
    ASSERT_TRUE(!ir_dominated_by(_1, _2));

    ASSERT_TRUE(!ir_dominates   (_2, _1));
    ASSERT_TRUE( ir_dominated_by(_2, _1));

    ir_node_cleanup(_2);
    ir_node_cleanup(_1);

    TEST_END_INFO
}

void dominates_condition()
{
    TEST_START_INFO

    ir_reset_internal_state();

    struct ir_node *body = ir_bin_init(TOK_PLUS, ir_sym_init(0), ir_sym_init(0));

    struct ir_node *_1 = ir_cond_init(body, 0);
    struct ir_node *_2 = ir_jump_init(0);
    struct ir_node *_3 = ir_jump_init(0);
    struct ir_node *_4 = ir_ret_init(0, ir_sym_init(0));

    ((struct ir_cond *) _1->ir)->target    = _2;
                        _1     ->next_else = _3;
    ((struct ir_jump *) _2->ir)->target    = _4;
    ((struct ir_jump *) _3->ir)->target    = _4;

    _1->next = _2;
    _2->next = _3;
    _3->next = _4;

    struct ir_node *f = ir_func_decl_init(D_T_INT, "f", NULL, _1);

    ir_dominator_tree(f->ir);
    /*
    printf("idom(1): %d\n", _1->idom->instr_idx);
    printf("idom(2): %d\n", _2->idom->instr_idx);
    printf("idom(3): %d\n", _3->idom->instr_idx);
    printf("idom(4): %d\n", _4->idom->instr_idx);
    */

    /* CFG:

              +-------+
              |   1   |
              +-------+
                 / \
                /   \
               /     \
              /       \
             /         \
            /           \
       +-------+     +-------+
       |   2   |     |   3   |
       +-------+     +-------+
            \            /
             \          /
              \        /
               \      /
                \    /
                 \  /
              +-------+
              |   4   |
              +-------+

       Dominator tree:

                  +-------+
             -----|   1   |-----
            /     +-------+     \
           /          |          \
       +-------+  +-------+  +-------+
       |   2   |  |   4   |  |   3   |
       +-------+  +-------+  +-------+
    */

    ASSERT_TRUE(_2->idom == _1);
//  ASSERT_TRUE(_4->idom == _1);
    ASSERT_TRUE(_3->idom == _1);

    ASSERT_TRUE(!ir_dominates(_2, _1));
    ASSERT_TRUE(!ir_dominates(_4, _1));
    ASSERT_TRUE(!ir_dominates(_3, _1));
    ASSERT_TRUE(!ir_dominates(_2, _4));
//  ASSERT_TRUE(!ir_dominates(_3, _4));

    /* ir_dump_cfg(stdout, f->ir);
    ir_dump_dom_tree(stdout, f->ir); */

    ir_node_cleanup(f);

    TEST_END_INFO
}

int main()
{
    dominates();
    dominates_condition();
}