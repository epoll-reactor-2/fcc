/* ir.c - Intermediate representation nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir.h"
#include "util/alloc.h"
#include "util/unreachable.h"
#include <assert.h>

/// Global state. -1 because of semantics of
/// index incrementing. This should be done before
/// instruction allocation. So it needed to have
/// indexing from 0.
static int32_t ir_instr_index = -1;

void ir_reset_internal_state()
{
    ir_instr_index = -1;
}

struct ir_node ir_node_init(enum ir_type type, void *ir)
{
    struct ir_node node = {
        .type      = type,
        .instr_idx = ir_instr_index,
        .ir        = ir
    };
    return node;
}

struct ir_node ir_alloca_init(enum data_type dt, int32_t idx)
{
    struct ir_alloca *ir = weak_calloc(1, sizeof (struct ir_alloca));
    ir->dt = dt;
    ir->idx = idx;
    ++ir_instr_index;
    return ir_node_init(IR_ALLOCA, ir);
}

struct ir_node ir_imm_bool_init(bool imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm_bool = imm;
    ir->type = IMM_BOOL;
    return ir_node_init(IR_IMM, ir);
}

struct ir_node ir_imm_char_init(char imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm_char = imm;
    ir->type = IMM_CHAR;
    return ir_node_init(IR_IMM, ir);
}

struct ir_node ir_imm_float_init(float imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm_float = imm;
    ir->type = IMM_FLOAT;
    return ir_node_init(IR_IMM, ir);
}

struct ir_node ir_imm_int_init(int32_t imm)
{
    struct ir_imm *ir = weak_calloc(1, sizeof (struct ir_imm));
    ir->imm_int = imm;
    ir->type = IMM_INT;
    return ir_node_init(IR_IMM, ir);
}


struct ir_node ir_sym_init(int32_t idx)
{
    struct ir_sym *ir = weak_calloc(1, sizeof (struct ir_sym));
    ir->idx = idx;
    return ir_node_init(IR_SYM, ir);
}

struct ir_node ir_store_imm_init(int32_t idx, struct ir_node imm)
{
    struct ir_store *ir = weak_calloc(1, sizeof (struct ir_store));
    ir->type = IR_STORE_IMM;
    ir->idx = idx;
    ir->body = imm;
    ++ir_instr_index;
    return ir_node_init(IR_STORE, ir);
}

struct ir_node ir_store_var_init(int32_t idx, int32_t var_idx)
{
    struct ir_store *ir = weak_calloc(1, sizeof (struct ir_store));
    ir->type = IR_STORE_VAR;
    ir->idx = idx;
    ir->body = ir_sym_init(var_idx);
    ++ir_instr_index;
    return ir_node_init(IR_STORE, ir);
}

struct ir_node ir_store_bin_init(int32_t idx, struct ir_node bin)
{
    assert(bin.type == IR_BIN && "Store expects binary expression in this context");
    struct ir_store *ir = weak_calloc(1, sizeof (struct ir_store));
    ir->type = IR_STORE_BIN;
    ir->idx = idx;
    ir->body = bin;
    ++ir_instr_index;
    return ir_node_init(IR_STORE, ir);
}

struct ir_node ir_bin_init(enum token_type op, struct ir_node lhs, struct ir_node rhs)
{
    assert(((
        lhs.type == IR_SYM ||
        lhs.type == IR_IMM
     ) && (
        rhs.type == IR_SYM ||
        rhs.type == IR_IMM
    )) && (
        "Binary operation expects variable or immediate value"
    ));
    struct ir_bin *ir = weak_calloc(1, sizeof (struct ir_bin));
    ir->op = op;
    ir->lhs = lhs;
    ir->rhs = rhs;
    return ir_node_init(IR_BIN, ir);
}

struct ir_node ir_label_init(int32_t idx)
{
    struct ir_label *ir = weak_calloc(1, sizeof (struct ir_label));
    ir->idx = idx;
    struct ir_node node = ir_node_init(IR_LABEL, ir);
    return node;
}

struct ir_node ir_jump_init(int32_t idx)
{
    struct ir_jump *ir = weak_calloc(1, sizeof (struct ir_jump));
    ir->idx = idx;
    ++ir_instr_index;
    return ir_node_init(IR_JUMP, ir);    
}

struct ir_node ir_cond_init(struct ir_node cond, int32_t goto_label)
{
    assert(cond.type == IR_BIN && "Only binary instruction supported as condition body");
    struct ir_cond *ir = weak_calloc(1, sizeof (struct ir_cond));
    ir->cond = cond;
    ir->goto_label = goto_label;
    ++ir_instr_index;
    return ir_node_init(IR_COND, ir);    
}

struct ir_node ir_ret_init(bool is_void, struct ir_node op)
{
    assert((
        op.type == IR_SYM ||
        op.type == IR_IMM ||
        (is_void && op.type == IR_RET_VOID)
    ) && (
        "Ret expects immediate value or variable"
    ));
    struct ir_ret *ir = weak_calloc(1, sizeof (struct ir_ret));
    ir->is_void = is_void;
    ir->op = op;
    /// Return operand is inline instruction.
    // if (!is_void) --ir_instr_index;
    ++ir_instr_index;
    return ir_node_init(is_void ? IR_RET_VOID : IR_RET, ir);    
}

struct ir_node ir_member_init(int32_t idx, int32_t field_idx)
{
    struct ir_member *ir = weak_calloc(1, sizeof (struct ir_member));
    ir->idx = idx;
    ir->field_idx = field_idx;
    return ir_node_init(IR_MEMBER, ir);
}

struct ir_node ir_array_access_init(int32_t idx, struct ir_node op)
{
    assert((
        op.type == IR_SYM ||
        op.type == IR_IMM
    ) && (
        "Array access expects immediate value or variable"
    ));
    struct ir_array_access *ir = weak_calloc(1, sizeof (struct ir_array_access));
    ir->idx = idx;
    ir->op = op;
    return ir_node_init(IR_ARRAY_ACCESS, ir);    
}

struct ir_node ir_type_decl_init(const char *name, uint64_t decls_size, struct ir_node *decls)
{
    __weak_debug({
        for (uint64_t i = 0; i < decls_size; ++i) {
            enum ir_type t = decls[i].type;
            assert((
                t == IR_ALLOCA ||
                t == IR_TYPE_DECL
            ) && (
                "Primitive or compound type as type field expected"
            ));
        }
    })
    struct ir_type_decl *ir = weak_calloc(1, sizeof (struct ir_type_decl));
    ir->name = name;
    ir->decls_size = decls_size;
    ir->decls = decls;
    return ir_node_init(IR_TYPE_DECL, ir);    
}

struct ir_node ir_func_decl_init(
    const char       *name,
    uint64_t          args_size,
    struct ir_node   *args,
    uint64_t          body_size,
    struct ir_node   *body
) {
    __weak_debug({
        for (uint64_t i = 0; i < args_size; ++i) {
            enum ir_type t = args[i].type;
            assert((t == IR_ALLOCA) && (
                "Function expects alloca instruction as parameter"
            ));
        }
    })
    struct ir_func_decl *ir = weak_calloc(1, sizeof (struct ir_func_decl));
    ir->name = name;
    ir->args_size = args_size;
    ir->args = args;
    ir->body_size = body_size;
    ir->body = body;
    return ir_node_init(IR_FUNC_DECL, ir);    
}

struct ir_node ir_func_call_init(const char *name, uint64_t args_size, struct ir_node  *args)
{
    __weak_debug({
        for (uint64_t i = 0; i < args_size; ++i) {
            enum ir_type t = args[i].type;
            assert((
                t == IR_SYM ||
                t == IR_IMM
            ) && (
                "Function call expression expects immediate value or variable"
            ));
        }
    })
    struct ir_func_call *ir = weak_calloc(1, sizeof (struct ir_func_call));
    ir->name = name;
    ir->args_size = args_size;
    ir->args = args;
    ++ir_instr_index;
    return ir_node_init(IR_FUNC_CALL, ir);    
}

static void ir_store_cleanup(struct ir_store *ir)
{
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
    if (!ir->is_void) ir_node_cleanup(ir->op);
}

static void ir_array_access_cleanup(struct ir_array_access *ir)
{
    ir_node_cleanup(ir->op);
}

static void ir_type_decl_cleanup(struct ir_type_decl *ir)
{
    for (uint64_t i = 0; i < ir->decls_size; ++i)
        ir_node_cleanup(ir->decls[i]);
}

static void ir_func_decl_cleanup(struct ir_func_decl *ir)
{
    for (uint64_t i = 0; i < ir->args_size; ++i)
        ir_node_cleanup(ir->args[i]);

    for (uint64_t i = 0; i < ir->body_size; ++i)
        ir_node_cleanup(ir->body[i]);
}
static void ir_func_call_cleanup(struct ir_func_call *ir)
{
    for (uint64_t i = 0; i < ir->args_size; ++i)
        ir_node_cleanup(ir->args[i]);
}

void ir_node_cleanup(struct ir_node ir)
{
    switch (ir.type) {
    case IR_ALLOCA:
    case IR_IMM:
    case IR_SYM:
    case IR_LABEL:
    case IR_JUMP:
    case IR_MEMBER: /// Fall through.
        /// Nothing to clean except ir.ir itself.
        break;
    case IR_STORE:        ir_store_cleanup(ir.ir); break;
    case IR_BIN:          ir_bin_cleanup(ir.ir); break;
    case IR_COND:         ir_cond_cleanup(ir.ir); break;
    case IR_RET:          ir_ret_cleanup(ir.ir); break;
    case IR_RET_VOID:     ir_ret_cleanup(ir.ir); break;
    case IR_ARRAY_ACCESS: ir_array_access_cleanup(ir.ir); break;
    case IR_TYPE_DECL:    ir_type_decl_cleanup(ir.ir); break;
    case IR_FUNC_DECL:    ir_func_decl_cleanup(ir.ir); break;
    case IR_FUNC_CALL:    ir_func_call_cleanup(ir.ir); break;
    default: weak_unreachable("Something went wrong.");
    }

    weak_free(ir.ir);
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