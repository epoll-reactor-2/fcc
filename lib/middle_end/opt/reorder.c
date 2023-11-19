/* reorder.c - Instruction reordering.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/opt/opt.h"
#include "util/vector.h"
#include <stddef.h>

/* This function follows alloca instructions chain and sets jump
   targets to instructions, that placed after alloca's. */
really_inline static void reindex(ir_vector_t *stmts)
{
    vector_foreach(*stmts, i) {
        struct ir_node *curr = vector_at(*stmts, i);

        /* We move allocas to most outer block, hence
            out of any loop. */
        if (curr->type == IR_ALLOCA)
            curr->meta.block_depth = 0;

        if (curr->type == IR_COND) {
            struct ir_cond *cond = curr->ir;
            uint64_t jump_idx = cond->goto_label;

            while (vector_at(*stmts, cond->goto_label)->type == IR_ALLOCA) {
                ++cond->goto_label;
                ++jump_idx;
                cond->target = vector_at(*stmts, jump_idx);
            }
        }

        if (curr->type == IR_JUMP) {
            struct ir_jump *jump = curr->ir;
            uint64_t jump_idx = jump->idx;

            while (vector_at(*stmts, jump->idx)->type == IR_ALLOCA) {
                ++jump->idx;
                ++jump_idx;
                jump->target = vector_at(*stmts, jump_idx);
            }
        }
    }
}

/* +-------+ -- next --> +-------+ -- next --> +-------+ -- next --> +-------+
   |   1   |             |   2   |             |  ir   |             |   3   |
   +-------+ <-- prev -- +-------+ <-- prev -- +-------+ <-- prev -- +-------+
  
   +-------+ -- next --> +-------+ -- next --> +-------+ -- next --> +-------+
   |   1   |             |  ir   |             |   2   |             |   3   |
   +-------+ <-- prev -- +-------+ <-- prev -- +-------+ <-- prev -- +-------+ */
really_inline static void swap(struct ir_node *ir)
{
    if (!ir->prev)
        return;

    if (!ir->prev->prev) {
        ir->prev->next = ir;
        ir->prev = NULL;
        return;
    }

    if (ir->type == IR_RET)
        return;

    if (ir->type != IR_ALLOCA)
        return;

    struct ir_node *_1 = ir->prev->prev;
    struct ir_node *_2 = ir->prev;
    struct ir_node *_3 = ir->next;

    _1->next = ir;
    ir->prev = _1;
    ir->next = _2;
    _2->prev = ir;
    _2->next = _3;
    _3->prev = _2;
}

/* This generally needed to force reordering algorithm to begin.
   If we start from first alloca statements, wi will fall
   into the senseless infinite recursion. */
really_inline static bool initial_move(struct ir_node **ir)
{
    (*ir) = (*ir)->next;
    if ((*ir))
        (*ir) = (*ir)->next;

    return (*ir);
}

/* This function traversing the list and group all
   alloca instructions together. This purpose of this
   optimization is easily determine, how many stack
   storage we must allocate for given function. */
void ir_opt_reorder(struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;

    ir_vector_t stmts = {0};

    while (it) {
        vector_push_back(stmts, it);
        it = it->next;
    }
    reindex(&stmts);

    it = decl->body;

    if (!initial_move(&it))
        return;

    struct ir_node *_ = it;
    swap(it);

    while (it) {
        it = _;
        it = it->next;
        while (it && it->type != IR_ALLOCA)
            it = it->next;

        while (it && it->prev != IR_ALLOCA)
            swap(it);
    }

    vector_free(stmts);
}