/* risc_v.h - RISC-V instructions and registers.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

/**********************************************
 **           Instruction codes              **
 **********************************************/

/* R type */
#define risc_v_R_add                (0b0110011 + (0 << 12)     )
#define risc_v_R_sub                (0b0110011 + (0 << 12) + (0b0100000 << 25))
#define risc_v_R_xor                (0b0110011 + (4 << 12)     )
#define risc_v_R_or                 (0b0110011 + (6 << 12)     )
#define risc_v_R_and                (0b0110011 + (7 << 12)     )
#define risc_v_R_sll                (0b0110011 + (1 << 12)     )
#define risc_v_R_srl                (0b0110011 + (5 << 12)     )
#define risc_v_R_sra                (0b0110011 + (5 << 12) + (0b0100000 << 25))
#define risc_v_R_slt                (0b0110011 + (2 << 12)     )
#define risc_v_R_sltu               (0b0110011 + (3 << 12)     )
/* I type */
#define risc_v_I_addi               (0b0010011                 )
#define risc_v_I_slli               (0b0010011 + (1 << 12)     )
#define risc_v_I_slti               (0b0010011 + (2 << 12)     )
#define risc_v_I_xori               (0b0010011 + (4 << 12)     )
#define risc_v_I_sltiu              (0b0010011 + (3 << 12)     )
#define risc_v_I_ori                (0b0010011 + (6 << 12)     )
#define risc_v_I_andi               (0b0010011 + (7 << 12)     )
#define risc_v_I_srli               (0b0010011 + (5 << 12)     )
#define risc_v_I_srai               (0b0010011 + (5 << 12) + (0b0100000 << 25))

#define risc_v_I_addiw              (0b0011011)
#define risc_v_I_slliw              (0b0011011 + (1 << 12)     )
#define risc_v_I_srliw              (0b0011011 + (5 << 12)     )
#define risc_v_I_sraiw              (0b0011011 + (5 << 12) + (0b0100000 << 25))
/* Load/store */
#define risc_v_I_lb                 (0b0000011                 )
#define risc_v_I_lh                 (0b0000011 + (1 << 12)     )
#define risc_v_I_lw                 (0b0000011 + (2 << 12)     )
#define risc_v_I_ld                 (0b0000011 + (3 << 12)     )
#define risc_v_I_lbu                (0b0000011 + (4 << 12)     )
#define risc_v_I_lhu                (0b0000011 + (5 << 12)     )
#define risc_v_I_lwu                (0b0000011 + (6 << 12)     )
#define risc_v_S_sb                 (0b0100011                 )
#define risc_v_S_sh                 (0b0100011 + (1 << 12)     )
#define risc_v_S_sw                 (0b0100011 + (2 << 12)     )
#define risc_v_S_sd                 (0b0100011 + (3 << 12)     )
/* Branches */
#define risc_v_B_beq                (0b1100011                 )
#define risc_v_B_bne                (0b1100011 + (1 << 12)     )
#define risc_v_B_blt                (0b1100011 + (4 << 12)     )
#define risc_v_B_bge                (0b1100011 + (5 << 12)     )
#define risc_v_B_bltu               (0b1100011 + (6 << 12)     )
#define risc_v_B_bgeu               (0b1100011 + (7 << 12)     )
/* Jumps */
#define risc_v_I_jal                (0b1101111                 )
#define risc_v_I_jalr               (0b1100111                 )
/* Misc */
#define risc_v_I_lui                (0b0110111                 )
#define risc_v_I_auipc              (0b0010111                 )
#define risc_v_I_ecall              (0b1110011                 )
#define risc_v_I_ebreak             (0b1110011 + (1 << 20)     )
/* M */
#define risc_v_M_mul                (0b0110011 + (1 << 25)     )
#define risc_v_M_div                (0b0110011 + (1 << 25) + (4 << 12))
#define risc_v_M_mod                (0b0110011 + (1 << 25) + (6 << 12))

/* Registers */
#define risc_v_reg_zero              0
#define risc_v_reg_ra                1
#define risc_v_reg_sp                2
#define risc_v_reg_gp                3
#define risc_v_reg_tp                4
#define risc_v_reg_t0                5
#define risc_v_reg_t1                6
#define risc_v_reg_t2                7
#define risc_v_reg_s0                8
#define risc_v_reg_s1                9
#define risc_v_reg_a0               10
#define risc_v_reg_a1               11
#define risc_v_reg_a2               12
#define risc_v_reg_a3               13
#define risc_v_reg_a4               14
#define risc_v_reg_a5               15
#define risc_v_reg_a6               16
#define risc_v_reg_a7               17
#define risc_v_reg_s2               18
#define risc_v_reg_s3               19
#define risc_v_reg_s4               20
#define risc_v_reg_s5               21
#define risc_v_reg_s6               22
#define risc_v_reg_s7               23
#define risc_v_reg_s8               24
#define risc_v_reg_s9               25
#define risc_v_reg_s10              26
#define risc_v_reg_s11              27
#define risc_v_reg_t3               28
#define risc_v_reg_t4               29
#define risc_v_reg_t5               30
#define risc_v_reg_t6               31