/* ir_dump.c - IR stringify function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_dump.h"
#include "front_end/lex/data_type.h"
#include "utility/diagnostic.h"
#include "utility/unreachable.h"
#include <assert.h>

static void ir_dump_node(FILE *mem, struct ir_node ir);

static void ir_dump_alloca(FILE *mem, struct ir_alloca *ir)
{
    fprintf(mem, "alloca %s %%%d", data_type_to_string(ir->dt), ir->idx);
}

static void ir_dump_imm(FILE *mem, struct ir_imm *ir)
{
    fprintf(mem, "$%d", ir->imm);
}

static void ir_dump_sym(FILE *mem, struct ir_imm *ir)
{
    fprintf(mem, "%%%d", ir->imm);
}

static void ir_dump_store(FILE *mem, struct ir_store *ir)
{
    fprintf(mem, "store %%%d ", ir->idx);
    ir_dump_node(mem, ir->body);
}

static void ir_dump_bin(FILE *mem, struct ir_bin *ir)
{
    const char *op = NULL;
    switch (ir->op) {
    case TOK_XOR:     op = "xor"; break;
    case TOK_BIT_AND: op = "and"; break;
    case TOK_BIT_OR:  op = "or";  break;
    case TOK_EQ:      op = "eq";  break;
    case TOK_NEQ:     op = "neq"; break;
    case TOK_GT:      op = "gt";  break;
    case TOK_LT:      op = "lt";  break;
    case TOK_GE:      op = "ge";  break;
    case TOK_LE:      op = "le";  break;
    case TOK_SHL:     op = "shl"; break;
    case TOK_SHR:     op = "shr"; break;
    case TOK_PLUS:    op = "add"; break;
    case TOK_MINUS:   op = "sub"; break;
    case TOK_STAR:    op = "mul"; break;
    case TOK_SLASH:   op = "div"; break;
    case TOK_MOD:     op = "mod"; break;
    default: weak_unreachable("Unknown operation");
    }

    ir_dump_node(mem, ir->lhs);
    fprintf(mem, " %s ", op);
    ir_dump_node(mem, ir->rhs);
}

static void ir_dump_label(FILE *mem, struct ir_label *ir)
{
    fprintf(mem, "\nL%d:", ir->idx);
}

static void ir_dump_jump(FILE *mem, struct ir_jump *ir)
{
    fprintf(mem, "jmp L%d", ir->idx);
}

static void ir_dump_cond(FILE *mem, struct ir_cond *ir)
{
    fprintf(mem, "if ");
    ir_dump_node(mem, ir->cond);
    fprintf(mem, " goto L%d", ir->goto_label);
}

static void ir_dump_ret(FILE *mem, struct ir_ret *ir)
{
    fprintf(mem, "ret ");
    ir_dump_node(mem, ir->op);
}

static void ir_dump_ret_void(FILE *mem)
{
    fprintf(mem, "ret");
}

static void ir_dump_member(FILE *mem, struct ir_member *ir)
{
    /// %1.0
    fprintf(mem, "%%%d.%d", ir->idx, ir->field_idx);
}

static void ir_dump_array_access(FILE *mem, struct ir_array_access *ir)
{
    /// %1[%2]
    /// %1[$123]
    (void) mem;
    (void) ir;
    weak_unreachable("todo: implement");
}

static void ir_dump_type_decl(FILE *mem, struct ir_type_decl *ir)
{
    fprintf(mem, "%%%s = {", ir->name);
    for (uint64_t i = 0; i < ir->decls_size; ++i) {
        fprintf(mem, "\n    ");
        ir_dump_node(mem, *(ir->decls + i));
    }
    fprintf(mem, "\n}");
}

static void ir_dump_func_decl(FILE *mem, struct ir_func_decl *ir)
{
    fprintf(mem, "fun %s(", ir->name);
    uint64_t size = ir->args_size;
    for (uint64_t i = 0; i < size; ++i) {
        ir_dump_alloca(mem, (ir->args + i)->ir);
        if (i < size - 1) {
            fprintf(mem, ", ");
        }
    }
    fprintf(mem, "):");

    size = ir->body_size;
    for (uint64_t i = 0; i < size; ++i) {
        struct ir_node node = *(ir->body + i);

        if (node.type != IR_LABEL)
            fprintf(mem, "\n% 8d:   ", node.instr_idx);
        ir_dump_node(mem, node);
    }
}

static void ir_dump_func_call(FILE *mem, struct ir_func_call *ir)
{
    fprintf(mem, "call %s(", ir->name);
    uint64_t size = ir->args_size;
    for (uint64_t i = 0; i < size; ++i) {
        struct ir_node node = *(ir->args + i);
        ir_dump_node(mem, node);
        if (i < size -1) {
            fprintf(mem, ", ");
        }
    }
    fprintf(mem, ")");
}

/* static */ void ir_dump_node(FILE *mem, struct ir_node ir)
{
    switch (ir.type) {
    case IR_ALLOCA:       ir_dump_alloca(mem, ir.ir); break;
    case IR_IMM:          ir_dump_imm(mem, ir.ir); break;
    case IR_SYM:          ir_dump_sym(mem, ir.ir); break;
    case IR_STORE:        ir_dump_store(mem, ir.ir); break;
    case IR_BIN:          ir_dump_bin(mem, ir.ir); break;
    case IR_LABEL:        ir_dump_label(mem, ir.ir); break;
    case IR_JUMP:         ir_dump_jump(mem, ir.ir); break;
    case IR_COND:         ir_dump_cond(mem, ir.ir); break;
    case IR_RET:          ir_dump_ret(mem, ir.ir); break;
    case IR_RET_VOID:     ir_dump_ret_void(mem); break;
    case IR_MEMBER:       ir_dump_member(mem, ir.ir); break;
    case IR_ARRAY_ACCESS: ir_dump_array_access(mem, ir.ir); break;
    case IR_TYPE_DECL:    ir_dump_type_decl(mem, ir.ir); break;
    case IR_FUNC_DECL:    ir_dump_func_decl(mem, ir.ir); break;
    case IR_FUNC_CALL:    ir_dump_func_call(mem, ir.ir); break;
    default: weak_unreachable("Something went wrong");
    }
}

int32_t ir_dump(FILE *mem, struct ir_func_decl *ir)
{
    if (mem == NULL || ir == NULL) return -1;

    ir_dump_func_decl(mem, ir);
    fprintf(mem, "\n");

    return 0;
}