/* ir_ops.c - Useful operations on IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir_ops.h"
#include "middle_end/ir/ir.h"

void ir_remove(struct ir_node **ir, struct ir_node **list_head)
{
    /* Note: conditional statements is never removed, so
             *next_else and *prev_else are unused. */
    if ((*ir)->next) {
        (*ir)->next->prev = (*ir)->prev;
    }

    if ((*ir)->prev) {
        (*ir)->prev->next = (*ir)->next;
    } else {
        (*ir) = (*ir)->next;
        (*list_head) = (*ir);
    }
}