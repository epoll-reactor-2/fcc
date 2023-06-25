

/* x86_64.c - x86_64 code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/x86_64.h"
#include "middle_end/ir.h"
#include "util/alloc.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include <assert.h>
#include <stdbool.h>

#define x86_total_regs  10
#define x86_reg_rax     -1
#define x86_reg_rdx     -2

static const char *x86_64_bit_regs[x86_total_regs] = {
    "%r10", "%r11", "%r12",
    "%r13", "%r9",  "%r8",
    "%rcx", "%rdx", "%rsi",
    "%rdi"
};

static const char *x86_32_bit_regs[x86_total_regs] = {
    "%r10d", "%r11d", "%r12d",
    "%r13d", "%r9d",  "%r8d",
    "%ecx",  "%edx",  "%esi",
    "%edi"
};

static const char *x86_16_bit_regs[x86_total_regs] = {
    "%r10b", "%r11b", "%r12b",
    "%r13b", "%r9b",  "%r8b",
    "%cl",   "%dl",   "%sil",
    "%dil"
};

static const char *x86_8_bit_regs[x86_total_regs] = {
    "%r10w", "%r11w", "%r12w",
    "%r13w", "%r9w",  "%r8w",
    "%cx",   "%dx",   "%si",
    "%di"
};

static bool x86_regs_status[x86_total_regs] = {1};


static const char *x86_alloc_type(enum data_type dt, int32_t idx)
{
    if (idx > 0) return "quad";
    switch (dt) {
    case D_T_BOOL:
    case D_T_CHAR: return "byte";
    case D_T_INT:  return "word";
    default:
        weak_unreachable("Should not reach there.");
    }    
}

/// Move everything to 64-bit register.
///
/// \todo: What is idx?
static const char *x86_load_postfix(enum data_type dt, int32_t idx)
{
    if (idx > 0) return "q";
    switch (dt) {
    case D_T_BOOL:
    case D_T_CHAR: return "zbq";
    case D_T_INT:  return "slq";
    default:
        weak_unreachable("Should not reach there.");
    }
}

static const char *x86_store_postfix(enum data_type dt, int32_t idx)
{
    if (idx > 0) return "q";
    switch (dt) {
    case D_T_BOOL:
    case D_T_CHAR: return "b";
    case D_T_INT:  return "l";
    default:
        weak_unreachable("Should not reach there.");
    }
}

/// \todo: What the fuck is RAX, RDX?
static const char *x86_get_reg(int32_t reg, enum data_type dt, int32_t idx)
{
    switch (reg) {
    case x86_reg_rax: {
        if (idx > 0)   return "%rax";
        switch (dt) {
        case D_T_BOOL:
        case D_T_CHAR: return "%al";
        case D_T_INT:  return "%eax";
        default:
            weak_unreachable("Should not reach there.");
        }
    } /// x86_reg_rax
    case x86_reg_rdx: {
        if (idx > 0)   return "%rdx";
        switch (dt) {
        case D_T_BOOL:
        case D_T_CHAR: return "%dl";
        case D_T_INT:  return "%edx";
        default:
            weak_unreachable("Should not reach there.");
        }
    } /// x86_reg_rdx
    default: {
        if (idx > 0)   return x86_64_bit_regs[reg];
        switch (dt) {
        case D_T_BOOL:
        case D_T_CHAR: return x86_8_bit_regs[reg];
        case D_T_INT:  return x86_32_bit_regs[reg];
        default:
            weak_unreachable("Should not reach there.");
        }
    } /// default
    }
}

static void x86_spill(int32_t reg)
{
    printf("\tpushq %s\n", x86_64_bit_regs[reg]);
}

static void x86_unspill(int32_t reg)
{
    printf("\tpushq %s\n", x86_64_bit_regs[reg]);
}

static void x86_spill_regs()
{
    for (uint64_t i = 0; i < x86_total_regs; ++i)
        x86_spill(i);
}

static void x86_unspill_regs()
{
    for (uint64_t i = 0; i < x86_total_regs; ++i)
        x86_unspill(i);
}



static int32_t x86_spilled_reg;

static int32_t x86_reg_alloc()
{
    for (uint64_t i = 0; i < x86_total_regs; ++i) {
        if (x86_regs_status[i]) {
            x86_regs_status[i] = 0;
            return i;
        }
    }

    int32_t reg = x86_spilled_reg % x86_total_regs;
    ++x86_spilled_reg;
    x86_spill(reg);
    return reg;
}

static void x86_reg_free(int32_t reg)
{
    if (reg == -1) return;
    if (x86_spilled_reg > 0) {
        x86_spilled_reg--;
        reg = (x86_spilled_reg % x86_total_regs);
        x86_unspill(reg);
    } else {
        x86_regs_status[reg] = 1;
    }
}



static void x86_gen_label(int32_t idx)
{
    printf("L%d:\n", idx);
}


static void x86_gen_load(const char *name, int32_t off, bool local)
{
    if (local)
        printf("%d(%%rbp)", off);
    else
        printf("%s(%%rip)", name);
}



static int32_t visit_ir_node(struct ir_node ir);

static int32_t visit_ir_alloca(struct ir_alloca *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_imm(struct ir_imm *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_sym(struct ir_imm *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_store(struct ir_store *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_bin(struct ir_bin *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_label(struct ir_label *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_jump(struct ir_jump *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_cond(struct ir_cond *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_ret(struct ir_ret *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_member(struct ir_member *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_array_access(struct ir_node *ir)
{
	(void) ir;
	return -1;
}

/// Store this in some internal state.
static int32_t visit_ir_type_decl(struct ir_type_decl *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_func_decl(struct ir_func_decl *ir)
{
	for (uint64_t i = 0; i < ir->body_size; ++i)
	    visit_ir_node(ir->body[i]);
    return -1;
}

static int32_t visit_ir_func_call(struct ir_func_call *ir)
{
	(void) ir;
	return -1;
}

static int32_t visit_ir_node(struct ir_node ir)
{
    switch (ir.type) {
    case IR_ALLOCA:       return visit_ir_alloca(ir.ir);
    case IR_IMM:          return visit_ir_imm(ir.ir);
    case IR_SYM:          return visit_ir_sym(ir.ir);
    case IR_STORE:        return visit_ir_store(ir.ir);
    case IR_BIN:          return visit_ir_bin(ir.ir);
    case IR_LABEL:        return visit_ir_label(ir.ir);
    case IR_JUMP:         return visit_ir_jump(ir.ir);
    case IR_COND:         return visit_ir_cond(ir.ir);
    case IR_RET:          return visit_ir_ret(ir.ir);
    case IR_RET_VOID:     return visit_ir_ret(ir.ir);
    case IR_MEMBER:       return visit_ir_member(ir.ir);
    case IR_ARRAY_ACCESS: return visit_ir_array_access(ir.ir);
    case IR_TYPE_DECL:    return visit_ir_type_decl(ir.ir);
    case IR_FUNC_DECL:    return visit_ir_func_decl(ir.ir);
    case IR_FUNC_CALL:    return visit_ir_func_call(ir.ir);
    default:
        weak_unreachable("Something went wrong");
    }
}

static void x86_gen_text()
{
    printf("\t.text\n");
}

static void x86_gen_data()
{
    printf("\t.data\n");
}

static void x86_gen_global_strings()
{
    /// \todo: Collect all strings and put them all to the begin of
    ///        assembly file.
    ///
    /// \todo: But before this implement strings in IR at all.
    ///
    /// \note: There is no strict requirement to have somehow strictly
    ///        collected data sections.
}

static void x86_gen_preamble()
{
    x86_gen_text();
    puts(
        "switch:\n"
        "\tpushq\t%rsi\n"
        "\tmovq\t%rdx,%rsi\n"
        "\tmovq\t%rax,%rbx\n"
        "\tcld\n"
        "\tlodsq\n"
        "\tmovq\t%rax,%rcx\n"
        "next:\n"
        "\tlodsq\n"
        "\tmovq\t%rax,%rdx\n"
        "\tlodsq\n"
        "\tcmpq\t%rdx,%rbx\n"
        "\tjnz\tno\n"
        "\tpopq\t%rsi\n"
        "\tjmp\t*%rax\n"
        "no:\n"
        "\tloop\tnext\n"
        "\tlodsq\n"
        "\tpopq\t%rsi\n"
        "\tjmp\t*%rax"
    );
}

void code_gen(struct ir *ir)
{
    x86_gen_preamble();
    x86_gen_global_strings();
	for (uint64_t i = 0; i < ir->decls_size; ++i)
		visit_ir_node(ir->decls[i]);
}