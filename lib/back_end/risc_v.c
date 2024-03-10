/* risc_v.c - RISC-V code generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v.h"
#include "middle_end/ir/ir.h"
#include "util/crc32.h"
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
int risc_v_ret     (                        ) { return risc_v_jalr(risc_v_reg_zero, risc_v_reg_ra, 0); }

/**********************************************
 **        Code generation routines          **
 **********************************************/

/* CRC-32 hash <=> symbol offset mapping.
   \
    Used in RISC-V generator to make calls. */
static hashmap_t fn_addr_map;
/* fn_offsets: String pointer value <=> symbol offset mapping.
   \
    Used in ELF generator. */
static struct    codegen_output *codegen_output;
static uint64_t  emitted_bytes;
/* How far we advanced from function begin. */
static uint64_t  fn_off;

static void put_sym(const char *sym)
{
    uint64_t hash = crc32_string(sym);
    hashmap_put(&codegen_output->fn_offsets, (uint64_t) sym, emitted_bytes);
    hashmap_put(&fn_addr_map, hash, emitted_bytes);
}

static uint64_t get_sym(const char *sym)
{
    uint64_t hash = crc32_string(sym);
    bool ok = 0;
    uint64_t off = hashmap_get(&fn_addr_map, hash, &ok);
    if (!ok)
        weak_fatal_error("Cannot get offset for `%s`", sym);
    return off;
}

static void replace_code(uint64_t at, int code)
{
    uint8_t *slice = (uint8_t *) &code;
    vector_at(codegen_output->instrs, at + 0) = slice[0];
    vector_at(codegen_output->instrs, at + 1) = slice[1];
    vector_at(codegen_output->instrs, at + 2) = slice[2];
    vector_at(codegen_output->instrs, at + 3) = slice[3];
}

static void put_code(int code)
{
    uint8_t *slice = (uint8_t *) &code;
    vector_push_back(codegen_output->instrs, slice[0]);
    vector_push_back(codegen_output->instrs, slice[1]);
    vector_push_back(codegen_output->instrs, slice[2]);
    vector_push_back(codegen_output->instrs, slice[3]);

    emitted_bytes += 4;
    fn_off += 4;
}

/**********************************************
 **              IR traversal                **
 **********************************************/

static char *current_fn;

static void emit_instr(struct ir_node *ir);
static void emit_alloca(unused struct ir_alloca *ir) {}
static void emit_alloca_array(unused struct ir_alloca_array *ir) {}
static void emit_imm(unused struct ir_imm *ir) {}
static void emit_sym(unused struct ir_sym *ir) {}
static void emit_store(struct ir_store *ir)
{
    emit_instr(ir->body);
    emit_instr(ir->idx);
}

static void emit_bin(unused struct ir_bin *ir) {}
static void emit_jump(unused struct ir_jump *ir) {}
static void emit_cond(unused struct ir_cond *ir) {}
static void emit_ret(unused struct ir_ret *ir) {}
static void emit_phi(unused struct ir_phi *ir) {}

static void emit_fn_call(struct ir_fn_call *ir)
{
    /* jal operates on relative offset. So if we
       refer to a defined above function, we use negative offset. */
    int off = get_sym(ir->name) - get_sym(current_fn);
    /* Take local function offset into account. */
    off -= fn_off;
    put_code(risc_v_jal(risc_v_reg_sp, off));
}

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

static void emit_fn_args(unused struct ir_fn_decl *fn) {}
static void emit_fn_body(struct ir_fn_decl *fn)
{
    struct ir_node *it = fn->body;
    while (it) {
        emit_instr(it);
        it = it->next;
    }
}

static void emit_fn(unused struct ir_fn_decl *fn)
{
    current_fn = fn->name;
    fn_off = 0;
    put_sym(fn->name);

    emit_fn_args(fn);
    emit_fn_body(fn);

    put_code(risc_v_ret());
}

/**********************************************
 **                Driver code               **
 **********************************************/
static uint64_t _entry_main_call_addr = 0x00;

static void emit_entry_fn()
{
    put_sym("_start");
    _entry_main_call_addr = emitted_bytes;
    /* We don't know where `main` is located at this
       point of codegen. Now we occupy space with some
       senseless instruction.

       Will be replaced with
       \
        jal ra, <main_offset> */
    put_code(0);
    /* Exit with 123 for now. */
    put_code(risc_v_addi(risc_v_reg_a0, risc_v_reg_zero, 123));
    /* 93 is __NR_exit? */
    put_code(risc_v_addi(risc_v_reg_a7, risc_v_reg_zero, 93));
    put_code(risc_v_ecall());
}

/**********************************************
 **                Driver code               **
 **********************************************/
void risc_v_gen(struct codegen_output *output, struct ir_unit *unit)
{
    codegen_output = output;
    emitted_bytes = 0;

    hashmap_init(&fn_addr_map, 512);

    emit_entry_fn();

    struct ir_node *ir = unit->fn_decls;
    while (ir) {
        emit_fn(ir->ir);
        ir = ir->next;
    }

    /* Replace previosly emitted 0x00 instruction in place
       of `main` call, because only now we know where `main`
       is located. */
    replace_code(
        _entry_main_call_addr,
        risc_v_jal(risc_v_reg_ra, get_sym("main"))
    );
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
