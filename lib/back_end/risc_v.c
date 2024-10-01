/* risc_v.c - RISC-V encoding.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/back_end.h"
#include "back_end/risc_v.h"

/**********************************************
 **          Register allocation             **
 **********************************************/

#define MAX_REGISTERS  32
#define FREE_REG_START  5  // Start from `t0` (register 5)
#define FREE_REG_END   31  // End at `t6` (register 31)

static int reg_lru[MAX_REGISTERS] = {0};

__attribute__ ((constructor)) static void init_lru()
{
    int idx = 0;
    for (int i = FREE_REG_START; i <= FREE_REG_END; i++) {
        reg_lru[idx++] = i;
    }
}

static void update_lru(int reg)
{
    int i;
    for (i = 0; i < MAX_REGISTERS; i++) {
        if (reg_lru[i] == reg) {
            break;
        }
    }
    /* Shift elements to the left */
    for (int j = i; j < MAX_REGISTERS - 1; j++) {
        reg_lru[j] = reg_lru[j + 1];
    }
    /* Place the used register at the end */
    reg_lru[MAX_REGISTERS - 1] = reg;
}

static int allocate_register()
{
    for (int i = FREE_REG_START; i <= FREE_REG_END; i++) {
        /* Reclaim the least recently used register */
        if (reg_lru[0] == i) {
            int reg = reg_lru[0];
            update_lru(reg);
            return reg;
        }
    }
    return -1;
}

/**********************************************
 **            RISC-V encoding               **
 **********************************************/

static void write_uint32_le_m(void *addr, uint32_t v)
{
    uint8_t *mem = (uint8_t *) addr;
    mem[0] = (v      ) & 0xFF;
    mem[1] = (v >>  8) & 0xFF;
    mem[2] = (v >> 16) & 0xFF;
    mem[3] = (v >> 24) & 0xFF;
}

static bool risc_v_is_valid_imm(int32_t imm)
{
    return (((int32_t) (((uint32_t) imm) << 20)) >> 20) == imm;
}

static void risc_v_20_imm_op(uint32_t op, int32_t reg, int32_t imm)
{
    uint8_t code[4] = {0};
    write_uint32_le_m(code, op | (reg << 7) | (imm & 0xFFFFF000));
    put(code, 4);
}

static void risc_v_jal(int reg, int off)
{
    union {
        uint8_t  code[4];
        uint32_t instr;
    } u;

    u.instr = risc_v_I_jal
            | ( (uint32_t) reg <<  7)
            | (((uint32_t)(off >>  1) & 0x3FF) << 21)
            | (((uint32_t)(off >> 11) & 0x1  ) << 20)
            | (((uint32_t)(off >> 12) & 0xFF ) << 12)
            | (((uint32_t)(off >> 20) & 0x1  ) << 31);
    put(u.code, 4);
}

/* Load [31:12] bits of the register from 20-bit imm, signextend & zero lower bits */
static void risc_v_lui(int32_t reg, int32_t imm)
{
    risc_v_20_imm_op(0x37, reg, imm);
}

/* Load PC + [31:12] imm to register */
static void risc_v_auipc(int32_t reg, int32_t imm)
{
    risc_v_20_imm_op(0x17, reg, imm);
}

static void risc_v_r_op(int op, int rds, int r1, int r2)
{
    uint8_t code[4] = {0};
    write_uint32_le_m(code, op | (rds << 7) | (r1 << 15) | (r2 << 20));
    put(code, 4);
}

/* I-type operation (sign-extended 12-bit immediate) */
static void risc_v_i_op_internal(int op, int rds, int r, uint32_t imm)
{
    uint8_t code[4];
    write_uint32_le_m(code, op | (rds << 7) | (r << 15) | (((uint32_t) imm) << 20));
    put(code, 4);
}

static void risc_v_s_op_internal(int op, int reg, int addr, int off)
{
    uint8_t code[4];
    write_uint32_le_m(
        code, op
            | ((off  & 0x1F)    <<  7)
            | ( addr            << 15)
            | ( reg             << 20)
            | ( ((uint32_t) off >>  5) << 25)
    );
    put(code, 4);
}

static void risc_v_s_op(int op, int reg, int addr, int off)
{
    if (risc_v_is_valid_imm(off)) {
        risc_v_s_op_internal(op, reg, addr, off);
    } else {
        /* TODO: Claim regs. */
    }
}

/* Set native register reg to sign-extended 32-bit imm */
static void risc_v_native_setreg32s(int reg, int imm)
{
    if (!risc_v_is_valid_imm(imm)) {
        /* Upper 20 bits aren't sign-extension. */
        if (imm & 0x800)
            /* Lower 12-bit part will sign-extend and subtract 0x1000 from LUI value */
            imm += 0x1000;
        risc_v_lui(reg, imm);
        if ((imm & 0xFFF) != 0) {
            risc_v_i_op_internal(risc_v_I_addi, reg, reg, imm & 0xFFF);
        }
    } else {
        risc_v_i_op_internal(risc_v_I_addi, reg, risc_v_reg_zero, imm & 0xFFF);
    }
}

static void risc_v_native_setreg32(int reg, int imm)
{
    risc_v_native_setreg32s(reg, imm);
}

static int risc_v_i_to_r(int op)
{
    return op | 0x20;
}

static int risc_v_is_load_op(int op)
{
    return (op & 0xFF) == 0x03;
}

static int64_t sign_extend(uint64_t val, uint8_t bits)
{
    return ((int64_t)(val << (64 - bits))) >> (64 - bits);
}

static void risc_v_i_op(int op, int rds, int r, int32_t imm)
{
    if (risc_v_is_valid_imm(imm)) {
        risc_v_i_op_internal(op, rds, r, imm);
    } else if (!risc_v_is_load_op(op)) {
        if ((op == risc_v_I_addi || op == risc_v_I_addiw) && risc_v_is_valid_imm(imm >> 1)) {
            /* Lower to two consequent addi. */
            risc_v_i_op_internal(op, rds, r, imm >> 1);
            risc_v_i_op_internal(op, rds, rds, imm - (imm >> 1));
        } else {
            fflush(stdout);
            /* Reclaim register, load 32-bit imm, use in R-type op. */
            int rtmp = allocate_register();
            if (rtmp == -1) {
                printf("No regs\n");
                fflush(stdout);
                abort();
            }
            printf("1 Allocated %d\n", rtmp);
            fflush(stdout);
            risc_v_native_setreg32(rtmp, imm);
            risc_v_r_op(risc_v_i_to_r(op), rds, r, rtmp);
            update_lru(rtmp);
        }
    } else {
        int32_t imm_lo = sign_extend(imm, 12);
        printf("%x sign extend %x\n", imm, imm_lo);
        int rtmp = allocate_register();
        if (rtmp == -1) {
            printf("No regs\n");
            fflush(stdout);
            abort();
        }
        printf("2 Allocated %d\n", rtmp);
        fflush(stdout);

        risc_v_lui(rtmp, imm - imm_lo);
        printf("lui %d, %x\n", rtmp, imm - imm_lo);

        risc_v_r_op(risc_v_R_add, rtmp, rtmp, r);
        printf("add %d, %d, %d\n", rtmp, rtmp, r);

        risc_v_i_op_internal(op, rds, rtmp, imm_lo);
        printf("lb %d, %d, %x\n", rds, rtmp, imm_lo);

        update_lru(rtmp);
    }
}

/**********************************************
 **         Generic instructions             **
 **********************************************/

void back_end_native_add(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_R_add, dst, reg1, reg2);
}

void back_end_native_addi(int dst, int reg1, int imm)
{
    risc_v_i_op(risc_v_I_addi, dst, reg1, imm);
}

void back_end_native_addiw(int dst, int reg1, int imm)
{
    risc_v_i_op(risc_v_I_addiw, dst, reg1, imm);
}

void back_end_native_sub(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_R_sub, dst, reg1, reg2);
}

void back_end_native_div(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_M_div, dst, reg1, reg2);
}

void back_end_native_mul(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_M_mul, dst, reg1, reg2);
}

void back_end_native_xor(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_R_xor, dst, reg1, reg2);
}

void back_end_native_and(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_R_and, dst, reg1, reg2);
}

void back_end_native_or(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_R_or, dst, reg1, reg2);
}

void back_end_native_sra(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_R_sra, dst, reg1, reg2);
}

void back_end_native_srl(int dst, int reg1, int reg2)
{
    risc_v_r_op(risc_v_R_srl, dst, reg1, reg2);
}

void back_end_native_li(int dst, int imm)
{
    back_end_native_addi(dst, risc_v_reg_zero, imm);
}

void back_end_native_lb(int dst, int addr, int off)
{
     risc_v_i_op(risc_v_I_lb, dst, addr, off);
}

void back_end_native_lbu(int dst, int addr, int off)
{
     risc_v_i_op(risc_v_I_lbu, dst, addr, off);
}

void back_end_native_lh(int dst, int addr, int off)
{
     risc_v_i_op(risc_v_I_lh, dst, addr, off);
}

void back_end_native_lhu(int dst, int addr, int off)
{
     risc_v_i_op(risc_v_I_lhu, dst, addr, off);
}

void back_end_native_lw(int dst, int addr, int off)
{
     risc_v_i_op(risc_v_I_lw, dst, addr, off);
}

void back_end_native_lwu(int dst, int addr, int off)
{
     risc_v_i_op(risc_v_I_lwu, dst, addr, off);
}

void back_end_native_ld(int dst, int addr, int off)
{
     risc_v_i_op(risc_v_I_ld, dst, addr, off);
}

void back_end_native_sb(int dst, int addr, int off)
{
    risc_v_s_op(risc_v_S_sb, dst, addr, off);
}

void back_end_native_sh(int dst, int addr, int off)
{
    risc_v_s_op(risc_v_S_sh, dst, addr, off);
}

void back_end_native_sw(int dst, int addr, int off)
{
    risc_v_s_op(risc_v_S_sw, dst, addr, off);
}

void back_end_native_sd(int dst, int addr, int off)
{
    risc_v_s_op(risc_v_S_sd, dst, addr, off);
}

void back_end_native_ret()
{
    risc_v_i_op(risc_v_I_jalr, risc_v_reg_zero, risc_v_reg_ra, 0);
}

void back_end_native_call(int off)
{
    risc_v_jal(risc_v_reg_ra, off);
}

void back_end_native_jmp_reg(int reg)
{
    risc_v_i_op(risc_v_I_jalr, risc_v_reg_zero, reg, 0);
}

void back_end_native_syscall_0(int syscall)
{
    back_end_native_li(risc_v_reg_a7, syscall);

    uint8_t code[4] = { risc_v_I_ecall, 0x00, 0x00, 0x00 };
    put(code, 4);
}

void back_end_native_syscall_1(int syscall, int _1)
{
    back_end_native_li(risc_v_reg_a0, _1);
    back_end_native_syscall_0(syscall);
}

void back_end_native_syscall_2(int syscall, int _1, int _2)
{
    back_end_native_li(risc_v_reg_a1, _2);
    back_end_native_syscall_1(syscall, _1);
}

void back_end_native_syscall_3(int syscall, int _1, int _2, int _3)
{
    back_end_native_li(risc_v_reg_a2, _3);
    back_end_native_syscall_2(syscall, _1, _2);
}

void back_end_native_syscall_4(int syscall, int _1, int _2, int _3, int _4)
{
    back_end_native_li(risc_v_reg_a3, _4);
    back_end_native_syscall_3(syscall, _1, _2, _3);
}

void back_end_native_syscall_5(int syscall, int _1, int _2, int _3, int _4, int _5)
{
    back_end_native_li(risc_v_reg_a4, _5);
    back_end_native_syscall_4(syscall, _1, _2, _3, _4);
}

void back_end_native_syscall_6(int syscall, int _1, int _2, int _3, int _4, int _5, int _6)
{
    back_end_native_li(risc_v_reg_a5, _6);
    back_end_native_syscall_5(syscall, _1, _2, _3, _4, _5);
}

static int align_to_16_bytes(int num)
{
    return (num + 15) & ~15;
}

void back_end_native_prologue(int stack_usage)
{
    int extra_stack_usage = align_to_16_bytes(stack_usage);

    back_end_native_addi(risc_v_reg_sp, risc_v_reg_sp, -(extra_stack_usage + 16));
    back_end_native_sd(risc_v_reg_ra, risc_v_reg_sp,    (extra_stack_usage +  8));
    back_end_native_sd(risc_v_reg_s0, risc_v_reg_sp,    (extra_stack_usage +  0));
    back_end_native_addi(risc_v_reg_s0, risc_v_reg_sp,  (extra_stack_usage + 16));
}

void back_end_native_epilogue(int stack_usage)
{
    int extra_stack_usage = align_to_16_bytes(stack_usage);

    back_end_native_ld(risc_v_reg_ra, risc_v_reg_sp,   (extra_stack_usage +  8));
    back_end_native_ld(risc_v_reg_s0, risc_v_reg_sp,   (extra_stack_usage +  0));
    back_end_native_addi(risc_v_reg_sp, risc_v_reg_sp, (extra_stack_usage + 16));
}