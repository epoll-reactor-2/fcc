/* regalloc.c - Register allocator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/regalloc.h"
#include "middle_end/ir/ir.h"
#include <assert.h>
#include <stdint.h>
#include <string.h>

/**********************************************
 **       Graph-coloring allocator           **
 **********************************************/

/* This sets theoretically possible size of registers and
   variables for static arrays. */
#define REG_ALLOC_VARS_LIMIT 512
#define REG_ALLOC_REGS_LIMIT  32

static uint64_t reg_alloc_max_regs =  -1;

struct interference_graph {
    int graph[REG_ALLOC_VARS_LIMIT][REG_ALLOC_VARS_LIMIT];
    int degree[REG_ALLOC_VARS_LIMIT];
};

struct live_range {
    int start;
    int end;
};

struct live_range_info {
    struct live_range ranges[REG_ALLOC_VARS_LIMIT];
    int               count;
};

struct reg_allocator {
    int  color[REG_ALLOC_VARS_LIMIT];
    bool spill[REG_ALLOC_VARS_LIMIT];
    int  reg_free[REG_ALLOC_REGS_LIMIT];
};

static void reg_alloc_add_edge(struct interference_graph *g, int u, int v)
{
    if (!g->graph[u][v]) {
        g->graph[u][v] = 1;
        g->graph[v][u] = 1;
        g->degree[u]++;
        g->degree[v]++;
    }
}

static void reg_alloc_build_graph(struct interference_graph *g, struct live_range_info *info)
{
    for (uint64_t i = 0; i < info->count; ++i) {
        for (uint64_t j = i + 1; j < info->count; ++j) {
            if (info->ranges[i].start <= info->ranges[j].end &&
                info->ranges[j].start <= info->ranges[i].end)
                reg_alloc_add_edge(g, i, j);
        }
    }
}

static void reg_alloc(struct interference_graph *g, struct reg_allocator *allocator)
{
    for (uint64_t i = 0; i < REG_ALLOC_VARS_LIMIT; ++i) {
        allocator->color[i] = -1;
        allocator->spill[i] =  0;
    }

    bool available[REG_ALLOC_REGS_LIMIT] = {0};

    for (uint64_t i = 0; i < REG_ALLOC_VARS_LIMIT; ++i) {
        for (uint64_t j = 0; j < reg_alloc_max_regs; ++j) {
            available[j] = 1;
        }

        for (uint64_t j = 0; j < REG_ALLOC_VARS_LIMIT; ++j) {
            if (g->graph[i][j] && allocator->color[j] != -1)
                available[allocator->color[j]] = 0;
        }

        int reg = -1;
        for (uint64_t j = 0; j < reg_alloc_max_regs; ++j) {
            if (available[j]) {
                reg = j;
                break;
            }
        }

        if (reg != -1)
            allocator->color[i] = reg;
        else
            allocator->spill[i] = 1;
    }
}

/**********************************************
 **        Allocator initialization          **
 **********************************************/

static void reg_alloc_store_op_idx(struct ir_node *ir, int *lhs, int *rhs)
{
    *lhs = -1;
    *rhs = -1;

    switch (ir->type) {
    case IR_SYM: {
        struct ir_sym *sym = ir->ir;
        *lhs = sym->idx;
        break;
    }
    case IR_BIN: {
        struct ir_bin *bin = ir->ir;

        if (bin->lhs->type == IR_SYM) {
            struct ir_sym *sym = bin->lhs->ir;
            *lhs = sym->idx;
        }

        if (bin->rhs->type == IR_SYM) {
            struct ir_sym *sym = bin->rhs->ir;
            *rhs = sym->idx;
        }

        break;
    }
    default:
        break;
    }
}

static void reg_alloc_live_range_store(struct live_range_info *info, struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    assert(store->idx->type == IR_SYM);

    struct ir_sym *sym = store->idx->ir;
    int            res = sym->idx;
    int            i   = ir->instr_idx; /* Usage place in code. */
    int            lhs = 0;
    int            rhs = 0;

    reg_alloc_store_op_idx(store->body, &lhs, &rhs);

    /* Result. */
    if (info->ranges[res].start == -1) {
        info->ranges[res].start = i;
    }
    info->ranges[res].end = i;

    /* Left argument. */
    if (lhs != -1) {
        if (info->ranges[lhs].start == -1) {
            info->ranges[lhs].start = i;
        }
        info->ranges[lhs].end = i;
    }

    /* Right argument. */
    if (rhs != -1) {
        if (info->ranges[rhs].start == -1) {
            info->ranges[rhs].start = i;
        }
        info->ranges[rhs].end = i;
    }
}

static void reg_alloc_live_ranges(struct live_range_info *info, struct ir_node *ir)
{
    for (uint64_t i = 0; i < REG_ALLOC_VARS_LIMIT; ++i) {
        info->ranges[i].start = -1;
        info->ranges[i].end   = -1;
    }

    while (ir) {
        if (ir->type == IR_STORE)
            reg_alloc_live_range_store(info, ir);

        ir = ir->next;
    }

    info->count = REG_ALLOC_VARS_LIMIT;
}

/**********************************************
 **       Register -> IR assignment          **
 **********************************************/

static void ir_insert_before(struct ir_node *curr, struct ir_node *new)
{
    struct ir_node *prev = curr->prev;

    prev->next = new;
    new->prev = prev;
    new->next = curr;
    curr->prev = new;

    memcpy(&new->meta, &curr->meta, sizeof (struct meta));
}

static int select_spill_reg(struct reg_allocator *allocator)
{
    for (int i = 0; i < reg_alloc_max_regs; i++) {
        if (!allocator->reg_free[i]) {
            return i;
        }
    }
    return -1;
}

/** @{                */
/**    push regN      */
/**    regN = 0       */
/**    pop regN       */
/**                   */
/** TODO: Update      */
/**       store index */
static void put_spill(struct ir_node *ir, struct reg_allocator *allocator, int reg)
{
    ir_insert_before(ir, ir_push_init(reg));
    /* TODO: Correct mark spill. */
    allocator->reg_free[reg] = 1;
}

static void put_reload(struct ir_node *ir, struct reg_allocator *allocator, int reg)
{
    ir_insert_before(ir, ir_pop_init(reg));
    /* TODO: Correct mark spill. */
    allocator->reg_free[reg] = 0;
}
/** @} */

/* TODO: Insert push and pop before and after live range bounds? */
/* TODO: What if one variable has two non-intersecting lifetimes? */
static void handle_spill(
    struct ir_node         *parent,
    struct ir_node         *ir,
    struct reg_allocator   *allocator,
    struct live_range_info *live_range
) {
    if (ir->type != IR_SYM)
        return;

    if (ir->claimed_reg != IR_NO_CLAIMED_REG)
        return;

    struct ir_sym *sym = ir->ir;
    if (allocator->spill[sym->idx]) {
        int reg_to_spill = select_spill_reg(allocator);

        if (reg_to_spill == -1)
            return;

        put_spill(parent, allocator, reg_to_spill);

        allocator->spill[sym->idx] = reg_to_spill;
        allocator->color[sym->idx] = reg_to_spill;

        put_reload(parent->next, allocator, reg_to_spill);

        parent->claimed_reg = reg_to_spill;
    }
}

static void reg_alloc_assign_claimed_reg(
    struct ir_node         *ir,
    struct reg_allocator   *allocator,
    struct live_range_info *live_range
) {
    switch (ir->type) {
    case IR_SYM: {
        struct ir_sym *sym = ir->ir;
        if (!allocator->spill[sym->idx])
            ir->claimed_reg = allocator->color[sym->idx];
        break;
    }
    case IR_ALLOCA: {
        struct ir_alloca *alloca = ir->ir;
        if (!allocator->spill[alloca->idx])
            ir->claimed_reg = allocator->color[alloca->idx];
        break;
    }
    case IR_STORE: {
        struct ir_store *store = ir->ir;
        reg_alloc_assign_claimed_reg(store->idx, allocator, live_range);
        reg_alloc_assign_claimed_reg(store->body, allocator, live_range);

        handle_spill(ir, store->idx, allocator, live_range);
        break;
    }
    case IR_BIN: {
        struct ir_bin *bin = ir->ir;
        reg_alloc_assign_claimed_reg(bin->lhs, allocator, live_range);
        reg_alloc_assign_claimed_reg(bin->rhs, allocator, live_range);

        handle_spill(bin->parent, bin->lhs, allocator, live_range);
        handle_spill(bin->parent, bin->rhs, allocator, live_range);
        break;
    }
    case IR_COND: {
        struct ir_cond *cond = ir->ir;
        reg_alloc_assign_claimed_reg(cond->cond, allocator, live_range);

        handle_spill(ir, cond->cond, allocator, live_range);
        break;
    }
    case IR_RET: {
        struct ir_ret *ret = ir->ir;
        if (ret->body)
            reg_alloc_assign_claimed_reg(ret->body, allocator, live_range);
        break;
    }
    default:
        break;
    }
}

static void reg_alloc_assign_claimed_regs(
    struct ir_node         *it,
    struct reg_allocator   *allocator,
    struct live_range_info *live_range
) {
    while (it) {
        reg_alloc_assign_claimed_reg(it, allocator, live_range);
        it = it->next;
    }
}

/**********************************************
 **                Traversal                 **
 **********************************************/

static void reg_alloc_dump_lifetimes(struct live_range_info *live_range)
{
    for (uint64_t i = 0; i < live_range->count; ++i) {
        if (live_range->ranges[i].start == -1 ||
            live_range->ranges[i].end   == -1 )
            break;

        printf(
            "Lifetime for t%-2lu = { %-2d - %-2d }\n",
            i,
            live_range->ranges[i].start,
            live_range->ranges[i].end
        );
    }
}

static void reg_alloc_fn(struct ir_fn_decl *ir)
{
    /* TODO: function args. */
    struct interference_graph graph           = {0};
    struct live_range_info    live_range_info = {0};
    struct reg_allocator      allocator       = {0};

    reg_alloc_live_ranges(&live_range_info, ir->body);
    reg_alloc_build_graph(&graph, &live_range_info);
    reg_alloc(&graph, &allocator);
    reg_alloc_assign_claimed_regs(ir->body, &allocator, &live_range_info);
    reg_alloc_dump_lifetimes(&live_range_info);
}

void ir_reg_alloc(struct ir_unit *unit, uint64_t hardware_regs)
{
    reg_alloc_max_regs = hardware_regs;

    struct ir_node *it = unit->fn_decls;
    while (it) {
        struct ir_fn_decl *decl = it->ir;
        reg_alloc_fn(decl);
        it = it->next;
    }
}