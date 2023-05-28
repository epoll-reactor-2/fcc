/* code_gen.c - Code generation entry point.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/code_gen.h"
#include "middle_end/ir.h"
#include "utility/alloc.h"
#include "utility/crc32.h"
#include "utility/hashmap.h"
#include "utility/unreachable.h"
#include <assert.h>

void visit_ir_alloca(ir_alloca_t *ir)
{
	(void) ir;
}

void visit_ir_imm(ir_imm_t *ir)
{
	(void) ir;
}

void visit_ir_sym(ir_imm_t *ir)
{
	(void) ir;
}

void visit_ir_store(ir_store_t *ir)
{
	(void) ir;
}

void visit_ir_bin(ir_bin_t *ir)
{
	(void) ir;
}

void visit_ir_label(ir_label_t *ir)
{
	(void) ir;
}

void visit_ir_jump(ir_jump_t *ir)
{
	(void) ir;
}

void visit_ir_cond(ir_cond_t *ir)
{
	(void) ir;
}

void visit_ir_ret(ir_ret_t *ir)
{
	(void) ir;
}

void visit_ir_member(ir_member_t *ir)
{
	(void) ir;
}

void visit_ir_array_access(ir_node_t *ir)
{
	(void) ir;
}

/// Store this in some internal state.
void visit_ir_type_decl(ir_type_decl_t *ir)
{
	(void) ir;
}

void visit_ir_func_decl(ir_func_decl_t *ir)
{
	(void) ir;
}

void visit_ir_func_call(ir_func_call_t *ir)
{
	(void) ir;
}

static void visit_ir_node(ir_node_t ir)
{
    switch (ir.type) {
    case IR_ALLOCA:       visit_ir_alloca(ir.ir); break;
    case IR_IMM:          visit_ir_imm(ir.ir); break;
    case IR_SYM:          visit_ir_sym(ir.ir); break;
    case IR_STORE:        visit_ir_store(ir.ir); break;
    case IR_BIN:          visit_ir_bin(ir.ir); break;
    case IR_LABEL:        visit_ir_label(ir.ir); break;
    case IR_JUMP:         visit_ir_jump(ir.ir); break;
    case IR_COND:         visit_ir_cond(ir.ir); break;
    case IR_RET:          visit_ir_ret(ir.ir); break;
    case IR_RET_VOID:     visit_ir_ret(ir.ir); break;
    case IR_MEMBER:       visit_ir_member(ir.ir); break;
    case IR_ARRAY_ACCESS: visit_ir_array_access(ir.ir); break;
    case IR_TYPE_DECL:    visit_ir_type_decl(ir.ir); break;
    case IR_FUNC_DECL:    visit_ir_func_decl(ir.ir); break;
    case IR_FUNC_CALL:    visit_ir_func_call(ir.ir); break;
    default: weak_unreachable("Something went wrong");
    }
}

void code_gen(ir_t *ir)
{
	for (uint64_t i = 0; i < ir->decls_size; ++i)
		visit_ir_node(ir->decls[i]);
}