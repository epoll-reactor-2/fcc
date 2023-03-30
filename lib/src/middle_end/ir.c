/* ir.c - Intermediate representation nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir.h"
#include "utility/alloc.h"
#include "utility/unreachable.h"
#include <assert.h>

/// Global state.
static int32_t ir_instr_index = 0;

void ir_reset_internal_state()
{
    ir_instr_index = 0;
}

ir_node_t ir_node_init(ir_type_e type, void *ir)
{
    ir_node_t node = {
        .type = type,
        .instr_idx = ir_instr_index++,
        .ir = ir
    };
    return node;
}

ir_node_t ir_alloca_init(data_type_e dt, int32_t idx)
{
    ir_alloca_t *ir = weak_calloc(1, sizeof(ir_alloca_t));
    ir->dt = dt;
    ir->idx = idx;
    return ir_node_init(IR_ALLOCA, ir);
}

ir_node_t ir_imm_init(int32_t imm)
{
    ir_imm_t *ir = weak_calloc(1, sizeof(ir_imm_t));
    ir->imm = imm;
    return ir_node_init(IR_IMM, ir);
}

ir_node_t ir_sym_init(int32_t idx)
{
    ir_sym_t *ir = weak_calloc(1, sizeof(ir_sym_t));
    ir->idx = idx;
    return ir_node_init(IR_SYM, ir);
}

ir_node_t ir_store_imm_init(int32_t idx, int32_t imm)
{
    ir_store_t *ir = weak_calloc(1, sizeof(ir_store_t));
    ir->type = IR_STORE_IMM;
    ir->idx = idx;
    ir->body = ir_imm_init(imm);
    /// The inline instruction was created above.
    --ir_instr_index;
    return ir_node_init(IR_STORE, ir);
}

ir_node_t ir_store_var_init(int32_t idx, int32_t var_idx)
{
    ir_store_t *ir = weak_calloc(1, sizeof(ir_store_t));
    ir->type = IR_STORE_VAR;
    ir->idx = idx;
    /// \todo: Some IR to variables (just number index...)
    ///        Or left immediate value and treat this as
    ///        variable index with IR_STORE_VAR.
    ir->body = ir_sym_init(var_idx);
    /// The inline instruction was created above.
    --ir_instr_index;
    return ir_node_init(IR_STORE, ir);
}

ir_node_t ir_store_bin_init(int32_t idx, ir_node_t bin)
{
    assert(bin.type == IR_BIN && "Store expects binary expression in this context");
    ir_store_t *ir = weak_calloc(1, sizeof(ir_store_t));
    ir->type = IR_STORE_BIN;
    ir->idx = idx;
    ir->body = bin;
    return ir_node_init(IR_STORE, ir);
}

ir_node_t ir_bin_init(tok_type_e op, ir_node_t lhs, ir_node_t rhs)
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
    ir_bin_t *ir = weak_calloc(1, sizeof(ir_bin_t));
    ir->op = op;
    ir->lhs = lhs;
    ir->rhs = rhs;
    return ir_node_init(IR_BIN, ir);
}

ir_node_t ir_label_init(int32_t idx)
{
    ir_label_t *ir = weak_calloc(1, sizeof(ir_label_t));
    ir->idx = idx;
    ir_node_t node = ir_node_init(IR_LABEL, ir);
    /// Goto label has no own instruction index.
    --ir_instr_index;
    return node;
}

ir_node_t ir_jump_init(int32_t idx)
{
    ir_jump_t *ir = weak_calloc(1, sizeof(ir_jump_t));
    ir->idx = idx;
    return ir_node_init(IR_JUMP, ir);    
}

ir_node_t ir_cond_init(ir_node_t cond, int32_t goto_label)
{
    assert(cond.type == IR_BIN && "Only binary instruction supported as condition body");
    ir_cond_t *ir = weak_calloc(1, sizeof(ir_cond_t));
    ir->cond = cond;
    ir->goto_label = goto_label;
    /// Condition always built from 3 inline instructions.
    ir_instr_index -=
        1 + /// LHS.
        1 + /// RHS.
        1 ; /// Goto label.
    return ir_node_init(IR_COND, ir);    
}

ir_node_t ir_ret_init(bool is_void, ir_node_t op)
{
    assert((
        op.type == IR_SYM ||
        op.type == IR_IMM
    ) && (
        "Ret expects immediate value or variable"
    ));
    ir_ret_t *ir = weak_calloc(1, sizeof(ir_ret_t));
    ir->is_void = is_void;
    ir->op = op;
    return ir_node_init(is_void ? IR_RET_VOID : IR_RET, ir);    
}

ir_node_t ir_member_init(int32_t idx, int32_t field_idx)
{
    ir_member_t *ir = weak_calloc(1, sizeof(ir_member_t));
    ir->idx = idx;
    ir->field_idx = field_idx;
    return ir_node_init(IR_MEMBER, ir);
}

ir_node_t ir_array_access_init(int32_t idx, ir_node_t op)
{
    assert((
        op.type == IR_SYM ||
        op.type == IR_IMM
    ) && (
        "Array access expects immediate value or variable"
    ));
    ir_array_access_t *ir = weak_calloc(1, sizeof(ir_array_access_t));
    ir->idx = idx;
    ir->op = op;
    return ir_node_init(IR_ARRAY_ACCESS, ir);    
}

ir_node_t ir_type_decl_init(const char *name, uint64_t decls_size, ir_node_t *decls)
{
#ifndef NDEBUG
    for (uint64_t i = 0; i < decls_size; ++i) {
        ir_type_e t = decls[i].type;
        assert((
            t == IR_ALLOCA ||
            t == IR_TYPE_DECL
        ) && (
            "Primitive or compound type as type field expected"
        ));
    }
#endif // NDEBUG
    ir_type_decl_t *ir = weak_calloc(1, sizeof(ir_type_decl_t));
    ir->name = name;
    ir->decls_size = decls_size;
    ir->decls = decls;
    return ir_node_init(IR_TYPE_DECL, ir);    
}

ir_node_t ir_func_decl_init(
    const char  *name,
    uint64_t     args_size,
    ir_node_t   *args,
    uint64_t     body_size,
    ir_node_t   *body
) {
#ifndef NDEBUG
    for (uint64_t i = 0; i < args_size; ++i) {
        ir_type_e t = args[i].type;
        assert((t == IR_ALLOCA) && (
            "Function expects alloca instruction as parameter"
        ));
    }
#endif // NDEBUG
    ir_func_decl_t *ir = weak_calloc(1, sizeof(ir_func_decl_t));
    ir->name = name;
    ir->args_size = args_size;
    ir->args = args;
    ir->body_size = body_size;
    ir->body = body;
    return ir_node_init(IR_FUNC_DECL, ir);    
}

ir_node_t ir_func_call_init(const char *name, uint64_t args_size, ir_node_t  *args)
{
#ifndef NDEBUG
    for (uint64_t i = 0; i < args_size; ++i) {
        ir_type_e t = args[i].type;
        assert((
            t == IR_SYM ||
            t == IR_IMM
        ) && (
            "Function call expression expects immediate value or variable"
        ));
    }
#endif // NDEBUG
    ir_func_call_t *ir = weak_calloc(1, sizeof(ir_func_call_t));
    ir->name = name;
    ir->args_size = args_size;
    ir->args = args;
    return ir_node_init(IR_FUNC_CALL, ir);    
}


static void ir_store_cleanup(ir_store_t *ir)
{
    ir_node_cleanup(ir->body);
}

static void ir_bin_cleanup(ir_bin_t *ir)
{
    ir_node_cleanup(ir->lhs);
    ir_node_cleanup(ir->rhs);
}

static void ir_cond_cleanup(ir_cond_t *ir)
{
    ir_node_cleanup(ir->cond);
}

static void ir_ret_cleanup(ir_ret_t *ir)
{
    if (!ir->is_void) ir_node_cleanup(ir->op);
}

static void ir_array_access_cleanup(ir_array_access_t *ir)
{
    ir_node_cleanup(ir->op);
}

static void ir_type_decl_cleanup(ir_type_decl_t *ir)
{
    for (uint64_t i = 0; i < ir->decls_size; ++i)
        ir_node_cleanup(ir->decls[i]);
}

static void ir_func_decl_cleanup(ir_func_decl_t *ir)
{
    for (uint64_t i = 0; i < ir->args_size; ++i)
        ir_node_cleanup(ir->args[i]);

    for (uint64_t i = 0; i < ir->body_size; ++i)
        ir_node_cleanup(ir->body[i]);
}
static void ir_func_call_cleanup(ir_func_call_t *ir)
{
    for (uint64_t i = 0; i < ir->args_size; ++i)
        ir_node_cleanup(ir->args[i]);
}

void ir_node_cleanup(ir_node_t ir)
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
    case IR_STORE: ir_store_cleanup(ir.ir); break;
    case IR_BIN: ir_bin_cleanup(ir.ir); break;
    case IR_COND: ir_cond_cleanup(ir.ir); break;
    case IR_RET: ir_ret_cleanup(ir.ir); break;
    case IR_RET_VOID: ir_ret_cleanup(ir.ir); break;
    case IR_ARRAY_ACCESS: ir_array_access_cleanup(ir.ir); break;
    case IR_TYPE_DECL: ir_type_decl_cleanup(ir.ir); break;
    case IR_FUNC_DECL: ir_func_decl_cleanup(ir.ir); break;
    case IR_FUNC_CALL: ir_func_call_cleanup(ir.ir); break;
    default: weak_unreachable("Something went wrong.");
    }

    weak_free(ir.ir);
}
