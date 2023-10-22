/* dead.c - Dead code elimination.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

/// This optimization is completely wrong.
/// Correct dead code elimination requires more
/// advanced techniques such as data dependence graph
/// and SSA.

#if 0
#include "middle_end/opt/opt.h"
#include "middle_end/ir/ir.h"
#include "util/alloc.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include "util/vector.h"
#include <assert.h>

struct dce_entry {
    uint64_t instr_idx;
    uint64_t sym_idx;
};

static vector_t(struct dce_entry) dead_stores;
static vector_t(int32_t)          live_instrs;
static hashmap_t                  alloca_stmts;



static void reset_hashmap(hashmap_t *map)
{
    if (map->buckets) {
        hashmap_destroy(map);
    }
    hashmap_init(map, 512);
}

static void alloca_put(struct ir_node *ir)
{
    struct ir_alloca *alloca = ir->ir;
    hashmap_put(&alloca_stmts, (uint64_t) alloca->idx, (uint64_t) ir);
}

static int32_t alloca_get(int32_t sym_idx)
{
    bool ok = 0;
    uint64_t addr = hashmap_get(&alloca_stmts, (uint64_t) sym_idx, &ok);

    if (!ok)
        weak_unreachable("Did I put alloca properly?");

    struct ir_node *ir = (struct ir_node *) addr;

    return ir->instr_idx;
}

static bool alloca_in_this_cfg(int32_t sym_idx)
{
    bool ok = 0;
    uint64_t value = hashmap_get(&alloca_stmts, sym_idx, &ok);
    struct ir_node *ir = (struct ir_node *) value;
    assert(ir->type == IR_ALLOCA);
    struct ir_alloca *alloca = ir->ir;

    return alloca->idx == sym_idx;
}

static void dce_reset()
{
    vector_clear(dead_stores);
    vector_clear(live_instrs);
}

static void dce_node(struct ir_node *ir);

static void dce_put(uint64_t instr_idx, uint64_t sym_idx)
{
    struct dce_entry e = {
        .instr_idx = instr_idx,
        .sym_idx   = sym_idx
    };

    vector_push_back(dead_stores, e);
}

/// This code is totally eliminated, when should not.
///
/// int main() {
///     int b = 2; /// Thrown out (wrong).
///     int a = 1; /// Thrown out (wrong).
///     int c = 3;
/// 
///     if (a + b) {
///         c = 4;
///     } else {
///         b = 5; // Thrown out (wrong).
///     }
/// 
///     return b;
/// }
static void dce_keep_alive_last(uint64_t sym_idx)
{
    int32_t alloca_idx = 0;
    int32_t live_idx   = 0;
    bool     found     = 0;

    vector_foreach(dead_stores, i) {
        struct dce_entry e = vector_at(dead_stores, i);

        if (e.sym_idx == sym_idx && alloca_in_this_cfg(e.sym_idx)) {
            alloca_idx = alloca_get(sym_idx);
            live_idx = e.instr_idx;
            found = 1;
            break;
            // printf("Entry (%ld, %ld)\n", e.instr_idx, e.sym_idx);
        }
    }

    if (!found) return;

    vector_push_back(live_instrs, live_idx);
    vector_push_back(live_instrs, alloca_idx);
}


static void dce_store(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;

    if (store->idx->type != IR_SYM)
        return;

    struct ir_sym *sym = store->idx->ir;
    dce_put(ir->instr_idx, sym->idx);

    switch (store->body->type) {
    case IR_IMM: {
        break;
    }
    case IR_SYM: {
        struct ir_sym *body = store->body->ir;
        dce_keep_alive_last(body->idx);
        break;
    }
    case IR_BIN:
        dce_node(store->body);
        break;
    default:
        break;
    }
}



static void dce_ret(struct ir_node *ir)
{
    struct ir_ret *ret = ir->ir;

    if (ret->is_void)
        return;

    if (ret->body->type != IR_SYM)
        return;

    struct ir_sym *sym = ret->body->ir;

    dce_keep_alive_last(sym->idx);
    /// We always keep return statement because we are
    /// focused on arithmetic instructions. Eliminating
    /// returns is really control flow optimizations job.
    vector_push_back(live_instrs, ir->instr_idx);
}

static void dce_bin(struct ir_node *ir)
{
    struct ir_bin *bin = ir->ir;

    if (bin->lhs->type == IR_SYM) {
        struct ir_sym *sym = bin->lhs->ir;
        dce_keep_alive_last(sym->idx);
    }

    if (bin->rhs->type == IR_SYM) {
        struct ir_sym *sym = bin->rhs->ir;
        dce_keep_alive_last(sym->idx);
    }
}

static void dce_fcall(struct ir_node *ir)
{
    /// Not our optimization case.
    vector_push_back(live_instrs, ir->instr_idx);
}

static void dce_cond(struct ir_node *ir)
{
    struct ir_cond *cond = ir->ir;
    dce_node(cond->cond);
    /// Not our optimization case.
    vector_push_back(live_instrs, ir->instr_idx);
}

static void dce_jmp(struct ir_node *ir)
{
    struct ir_jump *jmp = ir->ir;
    /// Not our optimization case.
    vector_push_back(live_instrs, ir->instr_idx);
    /// I am not sure.
    vector_push_back(live_instrs, jmp->target->instr_idx);
}



static void dce_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        alloca_put(ir);
        break;
    case IR_IMM:
    case IR_SYM:
    case IR_JUMP:
        dce_jmp(ir);
    case IR_MEMBER:
    case IR_TYPE_DECL:
    case IR_FUNC_DECL:
    case IR_FUNC_CALL:
        dce_fcall(ir);
        break;
    case IR_STORE:
        dce_store(ir);
        break;
    case IR_BIN:
        dce_bin(ir);
        break;
    case IR_RET:
    case IR_RET_VOID:
        dce_ret(ir);
        break;
    case IR_COND:
        dce_cond(ir);
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}

static void dce(struct ir_node *start)
{
    struct ir_node *it = start;
    uint64_t cfg_no = 0;

    reset_hashmap(&alloca_stmts);

    while (it) {
//        bool should_reset = 0;
//        should_reset |= it == start;
//        should_reset |= cfg_no != it->cfg_block_no;

//        if (should_reset)
//            dce_reset();

        dce_node(it);

        /*
        if (!it->next || it->next->cfg_block_no != cfg_no) {
            vector_foreach(live_instrs, i) {
                uint64_t instr_idx = vector_at(live_instrs, i);
                printf("Keep alive entry at idx %ld\n", instr_idx);
            }
            printf("\n");
        }
        */

//        cfg_no = it->cfg_block_no;
        it = it->next;
    }
}

static void remove_node(struct ir_node **ir, struct ir_node **head)
{
    /// Note: conditional statements is never removed, so
    ///       *next_else and *prev_else are unused.
    if ((*ir)->next) {
        (*ir)->next->prev = (*ir)->prev;
    }

    if ((*ir)->prev) {
        (*ir)->prev->next = (*ir)->next;
    } else {
        (*ir) = (*ir)->next;
        (*head) = (*ir);
    }
}

static int qsort_cmp(const void *lhs, const void *rhs)
{
    return *(int32_t *) lhs - *(int32_t *) rhs;
}

static void cut(struct ir_node **ir)
{
    struct ir_node *it = *ir;

    qsort(live_instrs.data, live_instrs.count, sizeof (int32_t), qsort_cmp);

    while (it) {
        struct ir_node *next_node = it->next;

        int32_t *instr = bsearch(
            &it->instr_idx,
            live_instrs.data,
            live_instrs.count,
            sizeof (int32_t),
            qsort_cmp
        );

        if (instr == NULL)
            remove_node(&it, ir);

        it = next_node;
    }
}

void ir_opt_dead_code_elimination(struct ir_func_decl *decl)
{
    dce(decl->body);
    cut(&decl->body);
}
#endif // 0