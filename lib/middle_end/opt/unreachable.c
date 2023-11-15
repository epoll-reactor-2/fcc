/* unreachable.c - Unreachable code remove.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/opt/opt.h"
#include "middle_end/ir/ir.h"

really_inline static void mark_visited(bool *visited, struct ir_node *ir)
{
    visited[ir->instr_idx] = 1;
}

really_inline static bool in_same_cfg_block(struct ir_node *l, struct ir_node *r)
{
    return l->cfg_block_no == r->cfg_block_no;
}

static void traverse(bool *visited, uint64_t *max_id, struct ir_node *ir)
{
    if (visited[ir->instr_idx]) return;

    if (*max_id < ir->instr_idx)
        *max_id = ir->instr_idx;

    switch (ir->type) {
    case IR_IMM:
    case IR_SYM:
    case IR_BIN:
    case IR_MEMBER:
    case IR_STORE:
    case IR_ALLOCA:
    case IR_ALLOCA_ARRAY:
    case IR_FUNC_CALL: {
        mark_visited(visited, ir);
        traverse(visited, max_id, ir->next);
        break;
    }
    case IR_JUMP: {
        struct ir_jump *jmp = ir->ir;
        mark_visited(visited, ir);
        traverse(visited, max_id, jmp->target);
        break;
    }
    case IR_COND: {
        struct ir_cond *cond = ir->ir;
        mark_visited(visited, ir);
        traverse(visited, max_id, cond->target);
        traverse(visited, max_id, vector_at(ir->cfg.succs, 0));
        // traverse(visited, max_id, ir->next_else);
        break;
    }
    case IR_RET:
    case IR_RET_VOID: {
        mark_visited(visited, ir);
        bool should_jump = ir->next;
        if (ir->next) {
            /* We continue walking over graph if
               1) Return statement has successor in other CFG block.
               2) Return statement has no jump successors. Even if jumps
                  are located after return, they were/will visit
                  as condition or other jump targets, so they are not
                  removed.

               Otherwise, all after return statement can be safely
               removed since it guaranteed to never be reached. */
            should_jump &= !in_same_cfg_block(ir, ir->next);
            should_jump &= ir->next->type != IR_JUMP;
        }
        if (should_jump)
            traverse(visited, max_id, ir->next);
        break;
    }
    default:
        break;
    }
}

static void cut(bool *visited, uint64_t siz, struct ir_node *ir)
{
    struct ir_node *it = ir;

    while (it) {
        if (ir->instr_idx <= siz && !visited[it->instr_idx]) {
            ir_remove(&it, &ir);
        }
        it = it->next;
    }
}

/* Traverse CFG and remove all unvisited nodes. */
void ir_opt_unreachable_code(struct ir_func_decl *decl)
{
    bool visited[8192] = {0};
    /* How many nodes potentially were visited. */
    uint64_t max_id = 0;

    traverse(visited, &max_id, decl->body);
    cut(visited, max_id, decl->body);
}