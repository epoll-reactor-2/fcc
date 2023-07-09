

/* x86_64.c - x86_64 code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/x86_64.h"
#include "middle_end/ir/ir.h"
#include "util/alloc.h"
#include "util/compiler.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include <assert.h>
#include <stdbool.h>
#include <string.h>

#define x86_total_regs  10
#define x86_reg_rax     -1
#define x86_reg_rdx     -2
#define x86_no_reg      -1

__weak_unused
static const char *x86_64_bit_regs[x86_total_regs] = {
    "%r10", "%r11", "%r12",
    "%r13", "%r9",  "%r8",
    "%rcx", "%rdx", "%rsi",
    "%rdi"
};

__weak_unused
static const char *x86_32_bit_regs[x86_total_regs] = {
    "%r10d", "%r11d", "%r12d",
    "%r13d", "%r9d",  "%r8d",
    "%ecx",  "%edx",  "%esi",
    "%edi"
};

__weak_unused
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

static bool        x86_regs_status[x86_total_regs] = {1};
static const char *x86_last_reg;

__weak_unused static const char *x86_alloc_type(enum data_type dt, int32_t idx)
{
    if (idx > 0) return "quad";
    switch (dt) {
    case D_T_BOOL:
    case D_T_CHAR: return "byte";
    case D_T_INT:  return "word";
    default:
        weak_unreachable("Unknown data type (numeric: %d).", dt);
    }    
}

/// Move everything to 64-bit register.
///
/// \todo: What is idx?
__weak_unused static const char *x86_load_postfix(enum data_type dt, int32_t idx)
{
    if (idx > 0) return "q";
    switch (dt) {
    case D_T_BOOL:
    case D_T_CHAR: return "zbq";
    case D_T_INT:  return "slq";
    default:
        weak_unreachable("Unknown data type (numeric: %d).", dt);
    }
}

__weak_unused static const char *x86_store_postfix(enum data_type dt, int32_t idx)
{
    if (idx > 0) return "q";
    switch (dt) {
    case D_T_BOOL:
    case D_T_CHAR: return "b";
    case D_T_INT:  return "l";
    default:
        weak_unreachable("Unknown data type (numeric: %d).", dt);
    }
}

/// \todo: What the fuck is RAX, RDX?
static const char *x86_get_reg(int32_t reg, enum data_type dt, int32_t indirection_lvl)
{
    switch (reg) {
    case x86_reg_rax: {
        if (indirection_lvl > 0)
            return "%rax";
        switch (dt) {
        case D_T_BOOL:
        case D_T_CHAR: return "%al";
        case D_T_INT:  return "%eax";
        default:
            weak_unreachable("Unknown data type (numeric: %d).", dt);
        }
    } /// x86_reg_rax
    case x86_reg_rdx: {
        if (indirection_lvl > 0)
            return "%rdx";
        switch (dt) {
        case D_T_BOOL:
        case D_T_CHAR: return "%dl";
        case D_T_INT:  return "%edx";
        default:
            weak_unreachable("Unknown data type (numeric: %d).", dt);
        }
    } /// x86_reg_rdx
    default: {
        if (indirection_lvl > 0)
            return x86_64_bit_regs[reg];
        switch (dt) {
        case D_T_BOOL:
        case D_T_CHAR: return x86_8_bit_regs[reg];
        case D_T_INT:  return x86_32_bit_regs[reg];
        default:
            weak_unreachable("Unknown data type (numeric: %d).", dt);
        }
    } /// default
    }
}

static void x86_spill(int32_t reg)
{
    printf("\tpushq\t%s\n", x86_64_bit_regs[reg]);
}

static void x86_unspill(int32_t reg)
{
    printf("\tpopq\t%s\n", x86_64_bit_regs[reg]);
}

__weak_unused static void x86_spill_regs()
{
    for (uint64_t i = 0; i < x86_total_regs; ++i)
        x86_spill(i);
}

__weak_unused static void x86_unspill_regs()
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

__weak_unused static void x86_reg_free(int32_t reg)
{
    if (reg == x86_no_reg) return;
    if (x86_spilled_reg > 0) {
        x86_spilled_reg--;
        reg = (x86_spilled_reg % x86_total_regs);
        x86_unspill(reg);
    } else {
        x86_regs_status[reg] = 1;
    }
}



__weak_unused static void x86_gen_label(int32_t idx)
{
    printf("L%d:\n", idx);
}


__weak_unused static void x86_gen_load(const char *name, int32_t off, bool local)
{
    if (local)
        printf("%d(%%rbp)", off);
    else
        printf("%s(%%rip)", name);
}

__weak_unused static void x86_gen_jump(int32_t label)
{
    printf("\tjmp\tL%d\n", label);
}


static uint64_t x86_sizeof(enum data_type dt)
{
    switch (dt) {
    case D_T_CHAR:
    case D_T_BOOL:  return 1;
    case D_T_INT:   return 4;
    case D_T_FLOAT: return 4;
    default:
        weak_unreachable("Unknown data type (numeric: %d).", dt);
    }
}


static void visit_ir_node(struct ir_node ir);

static void visit_ir_alloca(struct ir_alloca *ir)
{
    int32_t reg_idx = x86_reg_alloc();
    uint64_t size = x86_sizeof(ir->dt);
    const char *reg = x86_get_reg(reg_idx, ir->dt, 0);

    if (size < 1) size = 1;
    if (size > 8) size = 8;

    printf("\tsubq\t$%ld, %%rsp\n", size);
    printf("\tlea\t(%%rsp), %s\n", reg);

    x86_last_reg = reg;
}

static void visit_ir_imm(struct ir_imm *ir)
{
    int32_t reg_idx = x86_reg_alloc();
    const char *reg = x86_64_bit_regs[reg_idx];

    switch (ir->type) {
    case IMM_BOOL: {
        printf("\tmovzbq\t$%d, %s\n", ir->imm.__bool, reg);
        break;
    }
    case IMM_CHAR: {
        printf("\tmovzbq\t$%d, %s\n", ir->imm.__char, reg);
        break;
    }
    case IMM_FLOAT: {
        /// \todo: Move to section like this
        ///
        ///        .__float_%d:
        ///                .long 0x123456789 # double 0.333 (converted to integer)
        ///
        ///        movss __float_1(%rip), %xmm0
        break;
    }
    case IMM_INT: {
        printf("\tmovabsq\t$%d, %s\n", ir->imm.__int, reg);
        break;
    }
    default:
        weak_unreachable("Unknown immediate IR type (numeric: %d).", ir->type);
    }

    x86_last_reg = reg;
}

static void visit_ir_sym(struct ir_imm *ir)
{
    (void) ir;
}

static void visit_ir_store(struct ir_store *ir)
{
    visit_ir_node(ir->body);
}

static void visit_ir_bin(struct ir_bin *ir)
{
    visit_ir_node(ir->lhs);
    visit_ir_node(ir->rhs);
}

static void visit_ir_label(struct ir_label *ir)
{
    (void) ir;
}

static void visit_ir_jump(struct ir_jump *ir)
{
    (void) ir;
}

static void visit_ir_cond(struct ir_cond *ir)
{
    (void) ir;
}

static void visit_ir_ret(struct ir_ret *ir)
{
    /// \todo: Jump to some label with final return of register
    ///        value. For that we need to create and store some labels?...
    ///
    /// \note: %rax register is used for storing return values.
    if (ir->is_void) return;
    /// \todo: FUUUUUUUUUUCK
    if (x86_last_reg)
        printf("\tmovq\t%s, %%rax\n", x86_last_reg);
    else
        printf("\tmovq\t$0, %%rax\n");
}

static void visit_ir_member(struct ir_member *ir)
{
    (void) ir;
}

static void visit_ir_array_access(struct ir_node *ir)
{
    (void) ir;
}

/// Store this in some internal state.
static void visit_ir_type_decl(struct ir_type_decl *ir)
{
    (void) ir;
}



static void x86_fun_prologue(const char *name)
{
    /// \todo: Calculate offsets; it means
    ///        how much stack memory should be
    ///        allocated for all variables.
    ///
    ///        Maybe additional traverse IR statements
    ///        list could solve this.
    printf("\t.global %s\n", name);
    printf("%s:\n", name);
    printf("\tpushq\t%%rbp\n");
    printf("\tmovq\t%%rsp, %%rbp\n");
    /// \todo: Stack offset...
    printf("\tsubq\t$16, %%rsp\n");
}

static void x86_fun_epilogue(const char *name)
{
    /// \todo: Free stack memory, that was allocated
    ///        in prologue.

    if (!strcmp(name, "main")) {
        printf("\tmovq\t$60, %%rax\n");
        printf("\txor\t%%rdi, %%rdi\n");
        printf("\tsyscall\n");
    } else {
        printf("\taddq\t$16, %%rsp\n");
        printf("\tpopq\t%%rbp\n");
        printf("\tret\n");
    }
}

static void visit_ir_func_decl(struct ir_func_decl *ir)
{
    x86_fun_prologue(ir->name);

    for (uint64_t i = 0; i < ir->body_size; ++i)
        visit_ir_node(ir->body[i]);

    x86_fun_epilogue(ir->name);
}


static void visit_ir_func_call(struct ir_func_call *ir)
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
    default:
        weak_unreachable("Unknown IR type (numeric: %d)", ir.type);
    }
}

__weak_unused static void x86_gen_text()
{
    printf("\t.text\n");
}

__weak_unused static void x86_gen_data()
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
}

void code_gen(struct ir *ir)
{
    x86_gen_preamble();
    x86_gen_global_strings();
    for (uint64_t i = 0; i < ir->decls_size; ++i)
        visit_ir_node(ir->decls[i]);
}