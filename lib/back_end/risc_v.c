/* risc_v.c - RISC-V code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v.h"
#include "middle_end/ir/ir.h"
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <sys/syscall.h>

/**********************************************
 **         Instruction encoding             **
 **********************************************/
/* R type */
#define riscv_R_add                51 /* 0b110011 + (0 << 12) */
#define riscv_R_sub        1073741875 /* 0b110011 + (0 << 12) + (0x20 << 25) */
#define riscv_R_xor             16435 /* 0b110011 + (4 << 12) */
#define riscv_R_or              24627 /* 0b110011 + (6 << 12) */
#define riscv_R_and             28723 /* 0b110011 + (7 << 12) */
#define riscv_R_sll              4147 /* 0b110011 + (1 << 12) */
#define riscv_R_srl             20531 /* 0b110011 + (5 << 12) */
#define riscv_R_sra        1073762355 /* 0b110011 + (5 << 12) + (0x20 << 25) */
#define riscv_R_slt              8243 /* 0b110011 + (2 << 12) */
#define riscv_R_sltu            12339 /* 0b110011 + (3 << 12) */
/* I type */
#define riscv_I_addi               19 /* 0b0010011 */
#define riscv_I_xori            16403 /* 0b0010011 + (4 << 12) */
#define riscv_I_ori             24595 /* 0b0010011 + (6 << 12) */
#define riscv_I_andi            28691 /* 0b0010011 + (7 << 12) */
#define riscv_I_slli             4115 /* 0b0010011 + (1 << 12) */
#define riscv_I_srli            20499 /* 0b0010011 + (5 << 12) */
#define riscv_I_srai       1073762323 /* 0b0010011 + (5 << 12) + (0x20 << 25) */
#define riscv_I_slti             8211 /* 0b0010011 + (2 << 12) */
#define riscv_I_sltiu           12307 /* 0b0010011 + (3 << 12) */
/* Load/store */
#define riscv_I_lb                  3 /* 0b11 */
#define riscv_I_lh               4099 /* 0b11 + (1 << 12) */
#define riscv_I_lw               8195 /* 0b11 + (2 << 12) */
#define riscv_I_lbu             16387 /* 0b11 + (4 << 12) */
#define riscv_I_lhu             20483 /* 0b11 + (5 << 12) */
#define riscv_S_sb                 35 /* 0b0100011 */
#define riscv_S_sh               4131 /* 0b0100011 + (1 << 12) */
#define riscv_S_sw               8227 /* 0b0100011 + (2 << 12) */
/* Branches */
#define riscv_B_beq                99 /* 0b1100011 */
#define riscv_B_bne              4195 /* 0b1100011 + (1 << 12) */
#define riscv_B_blt             16483 /* 0b1100011 + (4 << 12) */
#define riscv_B_bge             20579 /* 0b1100011 + (5 << 12) */
#define riscv_B_bltu            24675 /* 0b1100011 + (6 << 12) */
#define riscv_B_bgeu            28771 /* 0b1100011 + (7 << 12) */
/* Jumps */
#define riscv_jal                 111 /* 0b1101111 */
#define riscv_jalr                103 /* 0b1100111 */
/* Misc */
#define riscv_lui                  55 /* 0b0110111 */
#define riscv_auipc                23 /* 0b0010111 */
#define riscv_ecall               115 /* 0b1110011 */
#define riscv_ebreak          1048691 /* 0b1110011 + (1 << 20) */
/* M */
#define riscv_m_mul          33554483 /* 0b0110011 + (1 << 25) */
#define riscv_m_div          33570867 /* 0b0110011 + (1 << 25) + (4 << 12) */
#define riscv_m_mod          33579059 /* 0b0110011 + (1 << 25) + (6 << 12) */

/* registers */
#define riscv_reg_zero    0
#define riscv_reg_ra      1
#define riscv_reg_sp      2
#define riscv_reg_gp      3
#define riscv_reg_tp      4
#define riscv_reg_t0      5
#define riscv_reg_t1      6
#define riscv_reg_t2      7
#define riscv_reg_s0      8
#define riscv_reg_s1      9
#define riscv_reg_a0     10
#define riscv_reg_a1     11
#define riscv_reg_a2     12
#define riscv_reg_a3     13
#define riscv_reg_a4     14
#define riscv_reg_a5     15
#define riscv_reg_a6     16
#define riscv_reg_a7     17
#define riscv_reg_s2     18
#define riscv_reg_s3     19
#define riscv_reg_s4     20
#define riscv_reg_s5     21
#define riscv_reg_s6     22
#define riscv_reg_s7     23
#define riscv_reg_s8     24
#define riscv_reg_s9     25
#define riscv_reg_s10    26
#define riscv_reg_s11    27
#define riscv_reg_t3     28
#define riscv_reg_t4     29
#define riscv_reg_t5     30
#define riscv_reg_t6     31

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

    return op + (rs1 << 15) + (rs2 << 20) +
           risc_v_extract_bits(imm, 11, 11,  7,  7) +
           risc_v_extract_bits(imm,  1,  4,  8, 11) +
           risc_v_extract_bits(imm,  5, 10, 25, 30) + (sign << 31);
}

int risc_v_encode_J(int op, int rd, int imm)
{
    int sign = 0;

    if (imm < 0) {
        sign = 1;
        imm = -imm;
        imm = (1 << 21) - imm;
    }
    return op + (rd << 7) +
           risc_v_extract_bits(imm,  1, 10, 21, 30) +
           risc_v_extract_bits(imm, 11, 11, 20, 20) +
           risc_v_extract_bits(imm, 12, 19, 12, 19) + (sign << 31);
}

int risc_v_encode_U(int op,  int rd,  int imm) { return op + (rd << 7) + risc_v_extract_bits(imm, 12, 31, 12, 31); }

#define RISC_V_OPCODE(x, t) \
    int risc_v_##x(int rd, int l, int r) { return risc_v_encode_##t(riscv_##t##_##x, rd, l, r); }

#define RISC_V_R_OPCODE(x) RISC_V_OPCODE(x, R)
#define RISC_V_I_OPCODE(x) RISC_V_OPCODE(x, I)
#define RISC_V_S_OPCODE(x) RISC_V_OPCODE(x, S)
#define RISC_V_B_OPCODE(x) RISC_V_OPCODE(x, B)

RISC_V_R_OPCODE(add)
RISC_V_R_OPCODE(sub)
RISC_V_R_OPCODE(or)
RISC_V_R_OPCODE(xor)
RISC_V_R_OPCODE(and)
RISC_V_R_OPCODE(sll)
RISC_V_R_OPCODE(srl)
RISC_V_R_OPCODE(sra)
RISC_V_R_OPCODE(slt)
RISC_V_R_OPCODE(sltu)

RISC_V_I_OPCODE(addi)
RISC_V_I_OPCODE(xori)
RISC_V_I_OPCODE(ori)
RISC_V_I_OPCODE(andi)
RISC_V_I_OPCODE(slli)
RISC_V_I_OPCODE(srli)
RISC_V_I_OPCODE(srai)
RISC_V_I_OPCODE(slti)
RISC_V_I_OPCODE(sltiu)
RISC_V_I_OPCODE(lb)
RISC_V_I_OPCODE(lh)
RISC_V_I_OPCODE(lw)
RISC_V_I_OPCODE(lbu)
RISC_V_I_OPCODE(lhu)

RISC_V_S_OPCODE(sb)
RISC_V_S_OPCODE(sh)
RISC_V_S_OPCODE(sw)

RISC_V_B_OPCODE(beq)
RISC_V_B_OPCODE(bne)
RISC_V_B_OPCODE(blt)
RISC_V_B_OPCODE(bge)
RISC_V_B_OPCODE(bltu)
RISC_V_B_OPCODE(bgeu)

/* Rest. */
int risc_v_jal     (int rd,           int imm) { return risc_v_encode_J(riscv_jal, rd, imm); }
int risc_v_jalr    (int rd,  int rs1, int imm) { return risc_v_encode_I(riscv_jalr, rd, rs1, imm); }
int risc_v_lui     (int rd,           int imm) { return risc_v_encode_U(riscv_lui, rd, imm); }
int risc_v_auipc   (int rd,           int imm) { return risc_v_encode_U(riscv_auipc, rd, imm); }
int risc_v_ecall   (                         ) { return risc_v_encode_I(riscv_ecall,  riscv_reg_zero, riscv_reg_zero, 0); }
int risc_v_ebreak  (                         ) { return risc_v_encode_I(riscv_ebreak, riscv_reg_zero, riscv_reg_zero, 1); }
int risc_v_nop     (                         ) { return risc_v_addi(riscv_reg_zero, riscv_reg_zero, 0); }
int risc_v_mul     (int rd, int rs1, int rs2 ) { return risc_v_encode_R(riscv_m_mul, rd, rs1, rs2); }
int risc_v_div     (int rd, int rs1, int rs2 ) { return risc_v_encode_R(riscv_m_div, rd, rs1, rs2); }
int risc_v_mod     (int rd, int rs1, int rs2 ) { return risc_v_encode_R(riscv_m_mod, rd, rs1, rs2); }

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