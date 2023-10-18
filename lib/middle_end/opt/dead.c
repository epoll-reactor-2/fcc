/* dead.c - Dead code elimination.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/opt/opt.h"
#include "middle_end/ir/ir.h"
#include "util/alloc.h"
#include "util/unreachable.h"
#include "util/vector.h"

struct dce_entry {
    uint64_t instr_idx;
    uint64_t sym_idx;
};

static vector_t(struct dce_entry) dead_stores;
static vector_t(uint64_t)         live_stores;

static void dce_reset()
{
    vector_clear(dead_stores);
    vector_clear(live_stores);
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
///     int a = 1; /// Throwed out (wrong).
///     int b = 2; /// Throwed out (wrong).
///     int c = 3;
/// 
///     if (a + b) {
///         c = 4;
///     } else {
///         b = 5; // Throwed out (wrong).
///     }
/// 
///     return b;
/// }
static void dce_keep_alive_last(uint64_t sym_idx)
{
    uint64_t live_idx = 0;
    bool     found    = 0;

    vector_foreach(dead_stores, i) {
        struct dce_entry e = vector_at(dead_stores, i);

        if (e.sym_idx == sym_idx) {
            live_idx = e.instr_idx;
            found = 1;
            // printf("Entry (%ld, %ld)\n", e.instr_idx, e.sym_idx);
        }
    }

    if (!found) return;

    vector_push_back(live_stores, live_idx);
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



static void dce_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
    case IR_IMM:
    case IR_SYM:
    case IR_JUMP:
    case IR_MEMBER:
    case IR_TYPE_DECL:
    case IR_FUNC_DECL:
    case IR_FUNC_CALL:
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
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}

void ir_opt_dead_code_elimination(struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;
    uint64_t cfg_no = 0;

    while (it) {
        bool should_reset = 0;
        should_reset |= it == decl->body;
        should_reset |= cfg_no != it->cfg_block_no;

        if (should_reset)
            dce_reset();

        dce_node(it);

        if (!it->next || it->next->cfg_block_no != cfg_no) {
            vector_foreach(live_stores, i) {
                uint64_t instr_idx = vector_at(live_stores, i);
                printf("Keep alive entry at idx %ld\n", instr_idx);
            }
            printf("\n");
        }

        cfg_no = it->cfg_block_no;
        it = it->next;
    }

    printf("\n");
}