/* risc_v.c - RISC-V code generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v.h"
#include "middle_end/ir/ir.h"
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <sys/syscall.h>

int risc_v_extract_bits(int imm, int i_start, int i_end, int d_start, int d_end)
{
    int v;

    if (d_end - d_start != i_end - i_start || i_start > i_end ||
        d_start > d_end)
        weak_fatal_error("Invalid bit copy");

    v = imm >> i_start;
    v = v & ((2 << (i_end - i_start)) - 1);
    v = v << d_start;
    return v;
}

int risc_v_hi(int val)
{
    if ((val & (1 << 11)) != 0)
        return val + 4096;
    return val;
}

int risc_v_lo(int val)
{
    if ((val & (1 << 11)) != 0)
        return (val & 0xFFF) - 4096;
    return val & 0xFFF;
}

int risc_v_encode_R(int op, int rd, int rs1, int rs2)
{
    return op + (rd << 7) + (rs1 << 15) + (rs2 << 20);
}

int risc_v_encode_I(int op, int rd, int rs1, int imm)
{
    if (imm > 2047 || imm < -2048)
        weak_fatal_error("Offset too large");

    if (imm < 0) {
        imm += 4096;
        imm &= (1 << 13) - 1;
    }
    return op + (rd << 7) + (rs1 << 15) + (imm << 20);
}

int risc_v_encode_S(int op, int rs1, int rs2, int imm)
{
    if (imm > 2047 || imm < -2048)
        weak_fatal_error("Offset too large");

    if (imm < 0) {
        imm += 4096;
        imm &= (1 << 13) - 1;
    }
    return op + (rs1 << 15) + (rs2 << 20) +
           risc_v_extract_bits(imm, 0,  4,  7, 11) +
           risc_v_extract_bits(imm, 5, 11, 25, 31);
}

int risc_v_encode_B(int op, int rs1, int rs2, int imm)
{
    int sign = 0;

    /* 13 signed bits, with bit zero ignored */
    if (imm > 4095 || imm < -4096)
        weak_fatal_error("Offset too large");

    if (imm < 0)
        sign = 1;

    return op + (sign << 31) + (rs1 << 15) + (rs2 << 20) +
           risc_v_extract_bits(imm, 11, 11,  7,  7) +
           risc_v_extract_bits(imm,  1,  4,  8, 11) +
           risc_v_extract_bits(imm,  5, 10, 25, 30);
}

int risc_v_encode_J(int op, int rd, int imm)
{
    int sign = 0;

    if (imm < 0) {
        sign = 1;
        imm = -imm;
        imm = (1 << 21) - imm;
    }
    return op + (sign << 31) + (rd << 7) +
           risc_v_extract_bits(imm,  1, 10, 21, 30) +
           risc_v_extract_bits(imm, 11, 11, 20, 20) +
           risc_v_extract_bits(imm, 12, 19, 12, 19);
}

int risc_v_encode_U(int op,  int rd,  int imm) { return op + (rd << 7) + risc_v_extract_bits(imm, 12, 31, 12, 31); }

#define risc_v_opcode(x, t) \
    int risc_v_##x(int rd, int l, int r) { return risc_v_encode_##t(risc_v_##t##_##x, rd, l, r); }

#define risc_v_r_opcode(x) risc_v_opcode(x, R)
#define risc_v_i_opcode(x) risc_v_opcode(x, I)
#define risc_v_s_opcode(x) risc_v_opcode(x, S)
#define risc_v_b_opcode(x) risc_v_opcode(x, B)

risc_v_r_opcode(add)
risc_v_r_opcode(sub)
risc_v_r_opcode(or)
risc_v_r_opcode(xor)
risc_v_r_opcode(and)
risc_v_r_opcode(sll)
risc_v_r_opcode(srl)
risc_v_r_opcode(sra)
risc_v_r_opcode(slt)
risc_v_r_opcode(sltu)

risc_v_i_opcode(addi)
risc_v_i_opcode(xori)
risc_v_i_opcode(ori)
risc_v_i_opcode(andi)
risc_v_i_opcode(slli)
risc_v_i_opcode(srli)
risc_v_i_opcode(srai)
risc_v_i_opcode(slti)
risc_v_i_opcode(sltiu)
risc_v_i_opcode(lb)
risc_v_i_opcode(lh)
risc_v_i_opcode(lw)
risc_v_i_opcode(lbu)
risc_v_i_opcode(lhu)

risc_v_s_opcode(sb)
risc_v_s_opcode(sh)
risc_v_s_opcode(sw)

risc_v_b_opcode(beq)
risc_v_b_opcode(bne)
risc_v_b_opcode(blt)
risc_v_b_opcode(bge)
risc_v_b_opcode(bltu)
risc_v_b_opcode(bgeu)

/* Rest. */
int risc_v_jal     (int rd,          int imm) { return risc_v_encode_J(risc_v_I_jal, rd, imm); }
int risc_v_jalr    (int rd, int rs1, int imm) { return risc_v_encode_I(risc_v_I_jalr, rd, rs1, imm); }
int risc_v_lui     (int rd,          int imm) { return risc_v_encode_U(risc_v_I_lui, rd, imm); }
int risc_v_auipc   (int rd,          int imm) { return risc_v_encode_U(risc_v_I_auipc, rd, imm); }
int risc_v_ecall   (                        ) { return risc_v_encode_I(risc_v_I_ecall,  risc_v_reg_zero, risc_v_reg_zero, 0); }
int risc_v_ebreak  (                        ) { return risc_v_encode_I(risc_v_I_ebreak, risc_v_reg_zero, risc_v_reg_zero, 1); }
int risc_v_nop     (                        ) { return risc_v_addi(risc_v_reg_zero, risc_v_reg_zero, 0); }
int risc_v_mul     (int rd, int rs1, int rs2) { return risc_v_encode_R(risc_v_M_mul, rd, rs1, rs2); }
int risc_v_div     (int rd, int rs1, int rs2) { return risc_v_encode_R(risc_v_M_div, rd, rs1, rs2); }
int risc_v_mod     (int rd, int rs1, int rs2) { return risc_v_encode_R(risc_v_M_mod, rd, rs1, rs2); }

/**********************************************
 **                Printers                  **
 **********************************************/
static FILE *code_stream;

unused static void report(const char *msg)
{
    perror(msg);
    exit(1);
}

fmt(1, 2) unused static void emit(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    vfprintf(code_stream, fmt, args);
    va_end(args);
}

/**********************************************
 **        Code generation routines          **
 **********************************************/
static void emit_alloca(unused struct ir_alloca *ir) {}
static void emit_alloca_array(unused struct ir_alloca_array *ir) {}
static void emit_imm(unused struct ir_imm *ir) {}
static void emit_sym(unused struct ir_sym *ir) {}
static void emit_store(struct ir_store *ir)
{
    (void) ir;
    /* Calculate everything using EAX/RAX, store by
       stack offset or register (variable map => stack offset). */
}

static void emit_bin(unused struct ir_bin *ir) {}
static void emit_jump(unused struct ir_jump *ir) {}
static void emit_cond(unused struct ir_cond *ir) {}
static void emit_ret(unused struct ir_ret *ir) {}
static void emit_fn_call(unused struct ir_fn_call *ir) {}
static void emit_phi(unused struct ir_phi *ir) {}



static void emit_instr(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:       emit_alloca(ir->ir); break;
    case IR_ALLOCA_ARRAY: emit_alloca_array(ir->ir); break;
    case IR_IMM:          emit_imm(ir->ir); break;
    case IR_SYM:          emit_sym(ir->ir); break;
    case IR_STORE:        emit_store(ir->ir); break;
    case IR_BIN:          emit_bin(ir->ir); break;
    case IR_JUMP:         emit_jump(ir->ir); break;
    case IR_COND:         emit_cond(ir->ir); break;
    case IR_RET:          emit_ret(ir->ir); break;
    case IR_FN_CALL:      emit_fn_call(ir->ir); break;
    case IR_PHI:          emit_phi(ir->ir); break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}

unused static void emit_fn_args(unused struct ir_fn_decl *decl) {}
unused static void emit_fn_body(struct ir_node *ir)
{
    while (ir) {
        emit_instr(ir);
        ir = ir->next;
    }
}

static void emit_fn(unused struct ir_fn_decl *fn) {}

/**********************************************
 **                Driver code               **
 **********************************************/
void risc_v_gen(FILE *stream, struct ir_unit *unit)
{
    (void) unit;

    code_stream = stream;

    struct ir_node *ir = unit->fn_decls;
    while (ir) {
        puts("");
        emit_fn(ir->ir);
        ir = ir->next;
    }
}

/*
Эти портреты безлики
Он написал их на чёрном холсте
Безобразным движением кисти

Эти картины тревожны
И он их прятал во тьме
Может вовсе не он был художник
А кто-то извне?

Все узоры
Пропитаны горем
В болезненной форме
В гнетущей тоске

Когда дрожь пробирает по коже
Когда мысли ничтожны
Взгляд понурый, поникший во мгле
Они снова берутся за краски

Однотонные мрачные краски
Краски дьявола
Они вместе рисуют смерть
Монохромно на чёрном холсте
*/
