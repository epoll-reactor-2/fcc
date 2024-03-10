#include "back_end/risc_v.h"

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
int risc_v_ret     (                        ) { return risc_v_jalr(risc_v_reg_zero, risc_v_reg_ra, 0); }