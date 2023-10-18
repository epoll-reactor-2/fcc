/* reorder.c - Instruction reordering.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/opt/opt.h"
#include "util/vector.h"
#include <stddef.h>

typedef vector_t(struct ir_node *) ir_vector_t;

/// We assume that vector index is match with contained
/// IR instruction index.
///
/// This function follows alloca instructions chain and sets jump
/// targets to instructions, that placed after alloca's.
__weak_really_inline static void reindex(ir_vector_t *stmts)
{
    vector_foreach(*stmts, i) {
        struct ir_node *curr = vector_at(*stmts, i);

        if (curr->type == IR_COND) {
            struct ir_cond *cond = curr->ir;
            struct ir_node *jump = vector_at(*stmts, cond->goto_label);
            while (jump->type == IR_ALLOCA) {
                ++cond->goto_label;
                jump = jump->next;
            }
            cond->target = jump;
        }

        if (curr->type == IR_JUMP) {
            struct ir_jump *jump = curr->ir;
            uint64_t jump_idx = jump->target->instr_idx;

            while (jump->target->type == IR_ALLOCA) {
                jump->target = vector_at(*stmts, jump_idx);
                ++jump->idx;
                ++jump_idx;
            }
        }
    }
}

/// +-------+ -- next --> +-------+ -- next --> +-------+ -- next --> +-------+
/// |   1   |             |   2   |             |  ir   |             |   3   |
/// +-------+ <-- prev -- +-------+ <-- prev -- +-------+ <-- prev -- +-------+
///
/// +-------+ -- next --> +-------+ -- next --> +-------+ -- next --> +-------+
/// |   1   |             |  ir   |             |   2   |             |   3   |
/// +-------+ <-- prev -- +-------+ <-- prev -- +-------+ <-- prev -- +-------+
__weak_really_inline static void swap(struct ir_node *ir)
{
    if (!ir->prev) {
        return;
    }

    if (!ir->prev->prev) {
        ir->prev->next = ir;
        ir->prev = NULL;
        return;
    }

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

/// This generally needed to force reordering algorithm to begin.
/// If we will start from first alloca statements, wi will fall
/// into the senseless infinite recursion.
__weak_really_inline static bool initial_move(struct ir_node **ir)
{
    (*ir) = (*ir)->next;
    if ((*ir))
        (*ir) = (*ir)->next;

    return (*ir);
}

/// This function traversing the list and group all
/// alloca instructions together. This purpose of this
/// optimization is easily determine, how many stack
/// storage we must allocate for given function.
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