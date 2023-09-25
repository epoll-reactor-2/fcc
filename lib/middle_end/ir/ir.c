/* ir.c - Intermediate representation nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "util/alloc.h"
#include "util/unreachable.h"
#include <assert.h>
#include <string.h>

/// Global state. -1 because of semantics of
/// index incrementing. This should be done before
/// instruction allocation. So it needed to have
/// indexing from 0.
static int32_t ir_instr_index = -1;

void ir_reset_internal_state()
{
    ir_instr_index = -1;
}

struct ir_node *ir_node_init(enum ir_type type, void *ir)
{
    struct ir_node *node = weak_calloc(1, sizeof (struct ir_node));
    node->type = type;
    node->instr_idx = ir_instr_index;
    node->ir = ir;
    /// Is not set for now.
    node->cfg_block_no = 0;
    return node;
}

struct ir_node *ir_alloca_init(enum data_type dt, bool ptr, int32_t idx)
{
    struct ir_alloca *ir = weak_calloc(1, sizeof (struct ir_alloca));
    ir->dt = dt;
    ir->ptr = ptr;
    ir->idx = idx;
    ++ir_instr_index;
    return ir_node_init(IR_ALLOCA, ir);
}

struct ir_node *ir_alloca_array_init(
    enum data_type  dt,
    uint64_t       *enclosure_lvls,
    uint64_t        enclosure_lvls_size,
    int32_t         idx
) {
    struct ir_alloca_array *ir = weak_calloc(1, sizeof (struct ir_alloca_array));
    ir->dt = dt;
    ir->enclosure_lvls_size = enclosure_lvls_size;
    ir->idx = idx;
    memcpy(ir->enclosure_lvls, enclosure_lvls, enclosure_lvls_size * sizeof (uint64_t));
    ++ir_instr_index;
    return ir_node_init(IR_ALLOCA_ARRAY, ir);
}

struct ir_node *ir_imm_init(enum ir_imm_type t, union ir_imm_val imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm = imm;
    ir->type = t;
    return ir_node_init(IR_IMM, ir);
}

struct ir_node *ir_imm_bool_init(bool imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm.__bool = imm;
    ir->type = IMM_BOOL;
    return ir_node_init(IR_IMM, ir);
}

struct ir_node *ir_imm_char_init(char imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm.__char = imm;
    ir->type = IMM_CHAR;
    return ir_node_init(IR_IMM, ir);
}

struct ir_node *ir_imm_float_init(float imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm.__float = imm;
    ir->type = IMM_FLOAT;
    return ir_node_init(IR_IMM, ir);
}

struct ir_node *ir_imm_int_init(int32_t imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm.__int = imm;
    ir->type = IMM_INT;
    return ir_node_init(IR_IMM, ir);
}


struct ir_node *ir_sym_init(int32_t idx)
{
    struct ir_sym *ir = weak_calloc(1, sizeof (struct ir_sym));
    ir->deref = 0;
    ir->idx = idx;
    return ir_node_init(IR_SYM, ir);
}

struct ir_node *ir_sym_ptr_init(int32_t idx)
{
    struct ir_sym *ir = weak_calloc(1, sizeof (struct ir_sym));
    ir->deref = 1;
    ir->idx = idx;
    return ir_node_init(IR_SYM, ir);
}

struct ir_node *ir_store_init(struct ir_node *idx, struct ir_node *body)
{
    assert((
        idx->type == IR_SYM
    ) && (
        "Store instruction expects symbol or array access operator as target"
    ));
    struct ir_store *ir = weak_calloc(1, sizeof (struct ir_store));
    ir->idx = idx;
    ir->body = body;
    if (body->type != IR_FUNC_CALL)
        ++ir_instr_index;
    return ir_node_init(IR_STORE, ir);
}

struct ir_node *ir_store_sym_init(int32_t idx, struct ir_node *body)
{
    return ir_store_init(ir_sym_init(idx), body);
}

struct ir_node *ir_bin_init(enum token_type op, struct ir_node *lhs, struct ir_node *rhs)
{
    assert(((
        lhs->type == IR_SYM ||
        lhs->type == IR_IMM
    ) && (
        rhs->type == IR_SYM ||
        rhs->type == IR_IMM
    )) && (
        "Binary operation expects variable, immediate value or array access operator"
    ));
    struct ir_bin *ir = weak_calloc(1, sizeof (struct ir_bin));
    ir->op = op;
    ir->lhs = lhs;
    ir->rhs = rhs;
    return ir_node_init(IR_BIN, ir);
}

struct ir_node *ir_jump_init(int32_t idx)
{
    struct ir_jump *ir = weak_calloc(1, sizeof (struct ir_jump));
    ir->idx = idx;
    ++ir_instr_index;
    return ir_node_init(IR_JUMP, ir);
}

struct ir_node *ir_cond_init(struct ir_node *cond, int32_t goto_label)
{
    assert(cond->type == IR_BIN && "Only binary instruction supported as condition body");
    struct ir_cond *ir = weak_calloc(1, sizeof (struct ir_cond));
    ir->cond = cond;
    ir->goto_label = goto_label;
    ++ir_instr_index;
    return ir_node_init(IR_COND, ir);
}

struct ir_node *ir_ret_init(bool is_void, struct ir_node *body)
{
    assert((
        body->type == IR_SYM ||
        body->type == IR_IMM ||
        (is_void && body->type == IR_RET_VOID)
    ) && (
        "Ret expects immediate value or variable"
    ));
    struct ir_ret *ir = weak_calloc(1, sizeof (struct ir_ret));
    ir->is_void = is_void;
    ir->body = body;
    /// Return operand is inline instruction.
    ++ir_instr_index;
    return ir_node_init(is_void ? IR_RET_VOID : IR_RET, ir);
}

struct ir_node *ir_member_init(int32_t idx, int32_t field_idx)
{
    struct ir_member *ir = weak_calloc(1, sizeof (struct ir_member));
    ir->idx = idx;
    ir->field_idx = field_idx;
    return ir_node_init(IR_MEMBER, ir);
}

struct ir_node *ir_type_decl_init(const char *name, struct ir_node *decls)
{
    __weak_debug({
        struct ir_node *it = decls;
        while (it) {
            enum ir_type t = it->type;
            assert((
                t == IR_ALLOCA ||
                t == IR_TYPE_DECL
            ) && (
                "Primitive or compound type as type field expected"
            ));
            it = it->next;
        }
    })
    struct ir_type_decl *ir = weak_calloc(1, sizeof (struct ir_type_decl));
    ir->name = name;
    ir->decls = decls;
    return ir_node_init(IR_TYPE_DECL, ir);
}

struct ir_node *ir_func_decl_init(
    enum data_type  ret_type,
    const char     *name,
    struct ir_node *args,
    struct ir_node *body
) {
    __weak_debug({
        struct ir_node *it = args;
        while (it) {
            enum ir_type t = it->type;
            assert((t == IR_ALLOCA) && (
                "Function expects alloca instruction as parameter"
            ));
            it = it->next;
        }
    })
    struct ir_func_decl *ir = weak_calloc(1, sizeof (struct ir_func_decl));
    ir->ret_type = ret_type;
    ir->name = name;
    ir->args = args;
    ir->body = body;
    return ir_node_init(IR_FUNC_DECL, ir);
}

struct ir_node *ir_func_call_init(const char *name, struct ir_node *args)
{
    __weak_debug({
        struct ir_node *it = args;
        while (it) {
            enum ir_type t = it->type;
            assert((
                t == IR_IMM ||
                t == IR_SYM
            ) && (
                "Function call expects symbol or immediate as parameter"
            ));
            it = it->next;
        }
    })
    struct ir_func_call *ir = weak_calloc(1, sizeof (struct ir_func_call));
    ir->name = name;
    ir->args = args;
    ++ir_instr_index;
    return ir_node_init(IR_FUNC_CALL, ir);
}

static void ir_store_cleanup(struct ir_store *ir)
{
    ir_node_cleanup(ir->idx);
    ir_node_cleanup(ir->body);
}

static void ir_bin_cleanup(struct ir_bin *ir)
{
    ir_node_cleanup(ir->lhs);
    ir_node_cleanup(ir->rhs);
}

static void ir_cond_cleanup(struct ir_cond *ir)
{
    ir_node_cleanup(ir->cond);
}

static void ir_ret_cleanup(struct ir_ret *ir)
{
    if (!ir->is_void) ir_node_cleanup(ir->body);
}

static void ir_type_decl_cleanup(struct ir_type_decl *ir)
{
    struct ir_node *it = ir->decls;
    while (it) {
        ir_node_cleanup(it);
        it = it->next;
    }
}

static void ir_func_decl_cleanup(struct ir_func_decl *ir)
{
    struct ir_node *it = ir->args;
    while (it) {
        ir_node_cleanup(it);
        it = it->next;
    }

    it = ir->body;
    while (it) {
        ir_node_cleanup(it);
        it = it->next;
    }
}
static void ir_func_call_cleanup(struct ir_func_call *ir)
{
    struct ir_node *it = ir->args;
    while (it) {
        ir_node_cleanup(it);
        it = it->next;
    }
}

void ir_node_cleanup(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
    case IR_ALLOCA_ARRAY:
    case IR_IMM:
    case IR_SYM:
    case IR_JUMP:
    case IR_MEMBER: /// Fall through.
        /// Nothing to clean except ir->ir itself.
        break;
    case IR_STORE:        ir_store_cleanup(ir->ir); break;
    case IR_BIN:          ir_bin_cleanup(ir->ir); break;
    case IR_COND:         ir_cond_cleanup(ir->ir); break;
    case IR_RET:          ir_ret_cleanup(ir->ir); break;
    case IR_RET_VOID:     ir_ret_cleanup(ir->ir); break;
    case IR_TYPE_DECL:    ir_type_decl_cleanup(ir->ir); break;
    case IR_FUNC_DECL:    ir_func_decl_cleanup(ir->ir); break;
    case IR_FUNC_CALL:    ir_func_call_cleanup(ir->ir); break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }

    if (ir->meta)
        weak_free(ir->meta);
    weak_free(ir->ir);
    weak_free(ir);
}

/*
She puffing on my weed
and getting high as fuck.

What I wanna do? Smoke'n fuck,
me, my niggas and gore of sluts.
Hang' all day... And puff.
No sleep just smoke'n fuck.

Now image this: every day a different bitch,
every joint a different bud, every city
different clubs.

All that I need is pussy & weed.
*/