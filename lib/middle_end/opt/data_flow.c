/* data_flow.c - Data flow elimination.
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

/* dd -- Data dependency. */
really_inline static void traverse_dd_chain(bool *visited, struct ir_node *it)
{
    ir_vector_t *ddgs = &it->ddg_stmts;
    vector_foreach(*ddgs, i) {
        struct ir_node *ddg = vector_at(*ddgs, i);
        if (!visited[ddg->instr_idx])
            mark_visited(visited, ddg);
    }
}

/* Walk over loop and mark statements above and below
   in bounds of loop (up to most outer) as needed. */
really_inline static void extend_loop(bool *visited, struct ir_node *ir)
{
    struct ir_node *it = ir;
    uint64_t loop_idx = ir->meta.global_loop_idx;

    while (it &&
           it->cfg.preds.count > 0 &&
           it->meta.global_loop_idx == loop_idx &&
           it->meta.block_depth > 0
    ) {
        mark_visited(visited, it);
        traverse_dd_chain(visited, it);
        it = it->prev;
    }

    it = ir;

    while (it &&
           it->next &&
           it->meta.global_loop_idx == loop_idx &&
           it->meta.block_depth > 0
    ) {
        mark_visited(visited, it);
        traverse_dd_chain(visited, it);
        it = it->next;
    }
}

static void traverse_ddg(bool *visited, struct ir_node *ir)
{
    ir_vector_t *ddgs = &ir->ddg_stmts;

    vector_foreach(*ddgs, i) {
        struct ir_node *ddg = vector_at(*ddgs, i);
        if (!visited[ddg->instr_idx]) {
            mark_visited(visited, ddg);
            extend_loop(visited, ddg);
            traverse_ddg(visited, ddg);
        }
    }
}

static void traverse_from_ret(bool *visited, struct ir_node *ir)
{
    mark_visited(visited, ir);
    traverse_ddg(visited, ir);
}

static void traverse(bool *visited, struct ir_node *ir)
{
    struct ir_node *it = ir;

    while (it) {
        switch (it->type) {
        case IR_RET:
            /* Return is start point for whole optimization. */
            traverse_from_ret(visited, it);
            break;
        case IR_FUNC_CALL:
            /* Raw function calls are not this optimizer case.
               Left them. */
            mark_visited(visited, it);
            break;
        default:
            break;
        }

        it = it->next;
    }
}

static void cut(bool *visited, struct ir_node *ir)
{
    struct ir_node *it = ir;

    while (it) {
        if (!visited[it->instr_idx])
            ir_remove(&it, &ir);
        if (it)
            it = it->next;
    }
}

void ir_opt_data_flow(struct ir_func_decl *ir)
{
    bool visited[8192] = {0};
    traverse(visited, ir->body);
    cut(visited, ir->body);
}