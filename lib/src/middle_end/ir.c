/* ir.c - Intermediate representation nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

 #include "middle_end/ir.h"
 #include "utility/alloc.h"

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
    ir_store_t *ir = weak_calloc(1, sizeof(ir_store_t));
    ir->type = IR_STORE_BINARY;
    ir->idx = idx;
    ir->body = bin;
    return ir_node_init(IR_STORE, ir);
}

ir_node_t ir_binary_init(tok_type_e op, ir_node_t lhs, ir_node_t rhs)
{
    ir_binary_t *ir = weak_calloc(1, sizeof(ir_binary_t));
    ir->op = op;
    ir->lhs = lhs;
    ir->rhs = rhs;
    return ir_node_init(IR_BINARY, ir);
}

ir_node_t ir_label_init(int32_t idx)
{
    ir_label_t *ir = weak_calloc(1, sizeof(ir_label_t));
    ir->idx = idx;
    return ir_node_init(IR_LABEL, ir);    
}

ir_node_t ir_jump_init(int32_t idx)
{
    ir_jump_t *ir = weak_calloc(1, sizeof(ir_jump_t));
    ir->idx = idx;
    return ir_node_init(IR_JUMP, ir);    
}

ir_node_t ir_cond_init(ir_binary_t cond, ir_label_t goto_label)
{
    ir_cond_t *ir = weak_calloc(1, sizeof(ir_cond_t));
    ir->cond = cond;
    ir->goto_label = goto_label;
    return ir_node_init(IR_COND, ir);    
}

ir_node_t ir_ret_init(bool is_void, ir_node_t op)
{
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
    return ir_node_init(IR_MEMBER   , ir);    
}

ir_node_t ir_array_access_init(int32_t idx, ir_node_t op)
{
    ir_array_access_t *ir = weak_calloc(1, sizeof(ir_array_access_t));
    ir->idx = idx;
    ir->op = op;
    return ir_node_init(IR_ARRAY_ACCESS, ir);    
}

ir_node_t ir_type_decl_init(const char *name, uint64_t decls_size, ir_node_t *decls)
{
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
    ir_func_call_t *ir = weak_calloc(1, sizeof(ir_func_call_t));
    ir->name = name;
    ir->args_size = args_size;
    ir->args = args;
    return ir_node_init(IR_FUNC_CALL, ir);    
}

void ir_node_cleanup(ir_node_t ir) { (void)ir; }
void ir_alloca_cleanup(ir_node_t ir) { (void)ir; }
void ir_imm_cleanup(ir_node_t ir) { (void)ir; }
void ir_sym_cleanup(ir_node_t ir) { (void)ir; }
void ir_store_cleanup(ir_node_t ir) { (void)ir; }
void ir_binary_cleanup(ir_node_t ir) { (void)ir; }
void ir_label_cleanup(ir_node_t ir) { (void)ir; }
void ir_jump_cleanup(ir_node_t ir) { (void)ir; }
void ir_cond_cleanup(ir_node_t ir) { (void)ir; }
void ir_ret_cleanup(ir_node_t ir) { (void)ir; }
void ir_member_cleanup(ir_node_t ir) { (void)ir; }
void ir_type_decl_cleanup(ir_node_t ir) { (void)ir; }
void ir_func_decl_cleanup(ir_node_t ir) { (void)ir; }
void ir_func_call_cleanup(ir_node_t ir) { (void)ir; }
