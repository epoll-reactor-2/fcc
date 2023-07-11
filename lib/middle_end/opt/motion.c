/* motion.c - Invariant code motion.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/opt/opt.h"

static void motion(struct ir_func_decl *decl)
{
    /// \todo
    ///
    /// 1) Determine loop head (condition) and tail (goto).
    ///
    /// 2) Go over each statement in the loop and check
    ///    if it is dominated by loop condition. If no,
    ///    move it out.
    ///
    ///    However, de-facto all statements in loop will
    ///    be dominated by condition.
    (void) decl;
}

void ir_opt_motion(struct ir_node *ir)
{
    struct ir_node *it = ir;
    while (it) {
        motion(it->ir);
        it = it->next;
    }
}