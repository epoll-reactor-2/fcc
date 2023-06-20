/* code_gen.c - Code generation entry point.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/code_gen.h"
#include "middle_end/ir.h"
#include "util/alloc.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include <assert.h>

void visit_ir_alloca(struct ir_alloca *ir)
{
	(void) ir;
}

void visit_ir_imm(struct ir_imm *ir)
{
	(void) ir;
}

void visit_ir_sym(struct ir_imm *ir)
{
	(void) ir;
}

void visit_ir_store(struct ir_store *ir)
{
	(void) ir;
}

void visit_ir_bin(struct ir_bin *ir)
{
	(void) ir;
}

void visit_ir_label(struct ir_label *ir)
{
	(void) ir;
}

void visit_ir_jump(struct ir_jump *ir)
{
	(void) ir;
}

void visit_ir_cond(struct ir_cond *ir)
{
	(void) ir;
}

void visit_ir_ret(struct ir_ret *ir)
{
	(void) ir;
}

void visit_ir_member(struct ir_member *ir)
{
	(void) ir;
}

void visit_ir_array_access(struct ir_node *ir)
{
	(void) ir;
}

/// Store this in some internal state.
void visit_ir_type_decl(struct ir_type_decl *ir)
{
	(void) ir;
}

void visit_ir_func_decl(struct ir_func_decl *ir)
{
	(void) ir;
}

void visit_ir_func_call(struct ir_func_call *ir)
{
	(void) ir;
}

static void visit_ir_node(struct ir_node ir)
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

void code_gen(struct ir *ir)
{
	for (uint64_t i = 0; i < ir->decls_size; ++i)
		visit_ir_node(ir->decls[i]);
}