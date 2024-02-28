/* risc_v.h - RISC-V code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_RISC_V_H
#define WEAK_COMPILER_BACKEND_RISC_V_H

#include <stdio.h>

/**********************************************
 **         Instruction encoding             **
 **********************************************/
/* R type */
#define risc_v_R_add                51 /* 0b110011 + (0 << 12) */
#define risc_v_R_sub        1073741875 /* 0b110011 + (0 << 12) + (0x20 << 25) */
#define risc_v_R_xor             16435 /* 0b110011 + (4 << 12) */
#define risc_v_R_or              24627 /* 0b110011 + (6 << 12) */
#define risc_v_R_and             28723 /* 0b110011 + (7 << 12) */
#define risc_v_R_sll              4147 /* 0b110011 + (1 << 12) */
#define risc_v_R_srl             20531 /* 0b110011 + (5 << 12) */
#define risc_v_R_sra        1073762355 /* 0b110011 + (5 << 12) + (0x20 << 25) */
#define risc_v_R_slt              8243 /* 0b110011 + (2 << 12) */
#define risc_v_R_sltu            12339 /* 0b110011 + (3 << 12) */
/* I type */
#define risc_v_I_addi               19 /* 0b0010011 */
#define risc_v_I_xori            16403 /* 0b0010011 + (4 << 12) */
#define risc_v_I_ori             24595 /* 0b0010011 + (6 << 12) */
#define risc_v_I_andi            28691 /* 0b0010011 + (7 << 12) */
#define risc_v_I_slli             4115 /* 0b0010011 + (1 << 12) */
#define risc_v_I_srli            20499 /* 0b0010011 + (5 << 12) */
#define risc_v_I_srai       1073762323 /* 0b0010011 + (5 << 12) + (0x20 << 25) */
#define risc_v_I_slti             8211 /* 0b0010011 + (2 << 12) */
#define risc_v_I_sltiu           12307 /* 0b0010011 + (3 << 12) */
/* Load/store */
#define risc_v_I_lb                  3 /* 0b11 */
#define risc_v_I_lh               4099 /* 0b11 + (1 << 12) */
#define risc_v_I_lw               8195 /* 0b11 + (2 << 12) */
#define risc_v_I_lbu             16387 /* 0b11 + (4 << 12) */
#define risc_v_I_lhu             20483 /* 0b11 + (5 << 12) */
#define risc_v_S_sb                 35 /* 0b0100011 */
#define risc_v_S_sh               4131 /* 0b0100011 + (1 << 12) */
#define risc_v_S_sw               8227 /* 0b0100011 + (2 << 12) */
/* Branches */
#define risc_v_B_beq                99 /* 0b1100011 */
#define risc_v_B_bne              4195 /* 0b1100011 + (1 << 12) */
#define risc_v_B_blt             16483 /* 0b1100011 + (4 << 12) */
#define risc_v_B_bge             20579 /* 0b1100011 + (5 << 12) */
#define risc_v_B_bltu            24675 /* 0b1100011 + (6 << 12) */
#define risc_v_B_bgeu            28771 /* 0b1100011 + (7 << 12) */
/* Jumps */
#define risc_v_I_jal               111 /* 0b1101111 */
#define risc_v_I_jalr              103 /* 0b1100111 */
/* Misc */
#define risc_v_I_lui                55 /* 0b0110111 */
#define risc_v_I_auipc              23 /* 0b0010111 */
#define risc_v_I_ecall             115 /* 0b1110011 */
#define risc_v_I_ebreak        1048691 /* 0b1110011 + (1 << 20) */
/* M */
#define risc_v_M_mul          33554483 /* 0b0110011 + (1 << 25) */
#define risc_v_M_div          33570867 /* 0b0110011 + (1 << 25) + (4 << 12) */
#define risc_v_M_mod          33579059 /* 0b0110011 + (1 << 25) + (6 << 12) */

/* Registers */
#define risc_v_reg_zero    0
#define risc_v_reg_ra      1
#define risc_v_reg_sp      2
#define risc_v_reg_gp      3
#define risc_v_reg_tp      4
#define risc_v_reg_t0      5
#define risc_v_reg_t1      6
#define risc_v_reg_t2      7
#define risc_v_reg_s0      8
#define risc_v_reg_s1      9
#define risc_v_reg_a0     10
#define risc_v_reg_a1     11
#define risc_v_reg_a2     12
#define risc_v_reg_a3     13
#define risc_v_reg_a4     14
#define risc_v_reg_a5     15
#define risc_v_reg_a6     16
#define risc_v_reg_a7     17
#define risc_v_reg_s2     18
#define risc_v_reg_s3     19
#define risc_v_reg_s4     20
#define risc_v_reg_s5     21
#define risc_v_reg_s6     22
#define risc_v_reg_s7     23
#define risc_v_reg_s8     24
#define risc_v_reg_s9     25
#define risc_v_reg_s10    26
#define risc_v_reg_s11    27
#define risc_v_reg_t3     28
#define risc_v_reg_t4     29
#define risc_v_reg_t5     30
#define risc_v_reg_t6     31

/**********************************************
 **         Instruction encoding             **
 **********************************************/

struct ir_unit;

void risc_v_gen(FILE *stream, struct ir_unit *unit);

#endif // WEAK_COMPILER_BACKEND_RISC_V_H
