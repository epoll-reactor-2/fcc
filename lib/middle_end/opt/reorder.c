/* reorder.c - Instruction reordering.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/opt/opt.h"
#include <stddef.h>

/// +-------+ -- next --> +-------+ -- next --> +-------+ -- next --> +-------+
/// |   1   |             |   2   |             |  ir   |             |   3   |
/// +-------+ <-- prev -- +-------+ <-- prev -- +-------+ <-- prev -- +-------+
///
/// +-------+ -- next --> +-------+ -- next --> +-------+ -- next --> +-------+
/// |   1   |             |  ir   |             |   2   |             |   3   |
/// +-------+ <-- prev -- +-------+ <-- prev -- +-------+ <-- prev -- +-------+
static void swap(struct ir_node *ir)
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

/// This function traversing the list and group all
/// alloca instructions together. This purpose of this
/// optimization is easily determine, how many stack
/// storage we must allocate for given function.
static void reorder(struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;

    it = it->next;
    it = it->next;

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
}

void ir_opt_reorder(struct ir_node *ir)
{
    struct ir_node *it = ir;
    while (it) {
        reorder(it->ir);
        it = it->next;
    }
}