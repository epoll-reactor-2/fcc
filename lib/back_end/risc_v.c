/* risc_v.c - RISC-V code generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v.h"
#include "back_end/risc_v_encode.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/regalloc.h"
#include "util/compiler.h"
#include "util/crc32.h"
#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <asm-generic/unistd.h>

/* Please note that RISC-V interpreter in Linux wants
   from us an asm-generic interface. */

/**********************************************
 **        Code generation routines          **
 **********************************************/

/* CRC-32 hash <=> symbol offset mapping.
   \
    Used in RISC-V generator to make calls. */
static hashmap_t fn_addr_map;
/* IR index <=> stack offset mapping.
   \
    Used to refer variables on stack. */
static hashmap_t var_map;
/* fn_offsets: String pointer value <=> symbol offset mapping.
   \
    Used in ELF generator. */
static struct    codegen_output *codegen_output;
static uint64_t  emitted_bytes;
/* How far we advanced from function begin. */
static uint64_t  fn_off;

static int risc_v_accum_reg = risc_v_reg_t0;

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

static void replace(uint64_t at, int code)
{
    uint8_t *slice = (uint8_t *) &code;
    vector_at(codegen_output->instrs, at + 0) = slice[0];
    vector_at(codegen_output->instrs, at + 1) = slice[1];
    vector_at(codegen_output->instrs, at + 2) = slice[2];
    vector_at(codegen_output->instrs, at + 3) = slice[3];
}

static void put(int code)
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
 **          Register allocation             **
 **********************************************/

static int allocatable_regs[] = {
    risc_v_reg_t0,
    risc_v_reg_t1,
    risc_v_reg_t2,
    risc_v_reg_t3,
    risc_v_reg_t4,
    risc_v_reg_t5,
    risc_v_reg_t6
};

really_inline static int reg_alloc_reg(struct ir_node *ir)
{
    assert(ir->claimed_reg != IR_NO_CLAIMED_REG);

    return allocatable_regs[ir->claimed_reg];
}

/**********************************************
 **              IR traversal                **
 **********************************************/

static char *current_fn;

static void emit_instr(struct ir_node *ir);
static void emit_alloca(unused struct ir_alloca *ir) {}
static void emit_alloca_array(unused struct ir_alloca_array *ir) {}

static void emit_imm(struct ir_imm *ir)
{
    switch (ir->type) {
    case IMM_BOOL:  break;
    case IMM_CHAR:  break;
    case IMM_FLOAT: break;
    case IMM_INT:   put(risc_v_li(risc_v_accum_reg, ir->imm.__int)); break;
    default:
        weak_fatal_error("Unknown immediate type: %d", ir->type);
    }
}

static void emit_sym(struct ir_node *ir)
{
    struct ir_sym *sym = ir->ir;

    bool ok = 0;
    uint64_t off = hashmap_get(&var_map, sym->idx, &ok);
    if (!ok)
        weak_fatal_error("Failed to get stack offset for %%%lu\n", sym->idx);

    switch (sym->type_info.dt) {
    case D_T_INT: put(risc_v_lw(reg_alloc_reg(ir), risc_v_reg_sp, -off)); break;
    default:
        break;
    }

    risc_v_accum_reg = reg_alloc_reg(ir);
}

/*  li    t0, 123
    addi  t1, sp, 25
    sw    t0, 0(t1) */
static void emit_store(struct ir_store *ir)
{
    if (ir->idx->type != IR_SYM)
        weak_fatal_error("TODO: Implement arrays");

    struct ir_sym *sym = ir->idx->ir;
    bool ok = 0;
    uint64_t off = hashmap_get(&var_map, sym->idx, &ok);
    if (!ok)
        weak_fatal_error("Failed to get stack offset for %%%lu\n", sym->idx);

    if (ir->body->type == IR_IMM) {
        struct ir_imm *imm = ir->body->ir;
        int i = imm->imm.__int;
        put(risc_v_lui(reg_alloc_reg(ir->idx), risc_v_hi(i)));
        put(risc_v_addi(reg_alloc_reg(ir->idx), risc_v_accum_reg, risc_v_lo(i)));
    }

    if (ir->body->type == IR_FN_CALL) {
        emit_instr(ir->body);
        put(risc_v_sw(risc_v_reg_sp, risc_v_accum_reg, -off));
    }

    if (ir->body->type == IR_BIN) {
        emit_instr(ir->body);
    }
}

/* TODO: Correct register allocation use. */
static void emit_bin(unused struct ir_bin *ir)
{
    emit_instr(ir->lhs);
    int lhs_reg = risc_v_accum_reg;

    emit_instr(ir->rhs);
    int rhs_reg = risc_v_accum_reg;

    switch (ir->op) {
    case TOK_MINUS: put(risc_v_sub(lhs_reg, lhs_reg, rhs_reg)); break;
    case TOK_PLUS:  put(risc_v_add(lhs_reg, lhs_reg, rhs_reg)); break;
    case TOK_STAR:  put(risc_v_mul(lhs_reg, lhs_reg, rhs_reg)); break;
    case TOK_SLASH: put(risc_v_div(lhs_reg, lhs_reg, rhs_reg)); break;
    default:
        weak_fatal_error("Unknown binary operator: %d\n", ir->op);
    }
}

static void emit_jump(unused struct ir_jump *ir) {}
static void emit_cond(unused struct ir_cond *ir) {}

static void emit_ret(struct ir_ret *ir)
{
    if (ir->body)
        emit_instr(ir->body);
}

static void emit_phi(unused struct ir_phi *ir) {}

static void emit_fn_call(struct ir_fn_call *ir)
{
    /* jal operates on relative offset. So if we
       refer to a defined above function, we use negative offset. */
    int off = get_sym(ir->name) - get_sym(current_fn);
    /* Take local function offset into account. */
    off -= fn_off;
    put(risc_v_jal(risc_v_reg_sp, off));
}

static void emit_instr(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:       emit_alloca(ir->ir); break;
    case IR_ALLOCA_ARRAY: emit_alloca_array(ir->ir); break;
    case IR_IMM:          emit_imm(ir->ir); break;
    case IR_SYM:          emit_sym(ir); break;
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

static uint64_t _stack_bytes_used = 0x00;

/* We want to know how much space on stack we will
   need. `sp`, `ra` registers pushed and all declared
   variables inside a function body.

   TODO: Function arguments >= 5 or 6 also goes to stack. */
static void calculate_stack_usage(struct ir_fn_decl *fn)
{
    _stack_bytes_used = 0x00;
    _stack_bytes_used += 8; /* sp */
    _stack_bytes_used += 8; /* ra */

    struct ir_node *it = fn->body;

    while (it) {
        if (it->type == IR_ALLOCA) {
            struct ir_alloca *a = it->ir;
            hashmap_put(&var_map, a->idx, _stack_bytes_used);
            _stack_bytes_used += data_type_size[a->dt];
        }

        /* TODO: IR_ALLOCA_ARRAY */

        it = it->next;
    }
}

static void emit_prologue()
{
    put(risc_v_addi(risc_v_reg_sp, risc_v_reg_sp, -_stack_bytes_used));
    put(risc_v_sd(risc_v_reg_sp, risc_v_reg_sp, 0));
    put(risc_v_sd(risc_v_reg_sp, risc_v_reg_ra, 8));
}
/* TODO: Follow some convention about return values. Most compilers
         stores return value in `a0` or `a5`. */
static void emit_epilogue()
{
    put(risc_v_ld(risc_v_reg_ra, risc_v_reg_sp, 8));
    put(risc_v_ld(risc_v_reg_sp, risc_v_reg_sp, 0));
    put(risc_v_addi(risc_v_reg_sp, risc_v_reg_sp, _stack_bytes_used));
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

    calculate_stack_usage(fn);
    emit_prologue();

    emit_fn_args(fn);
    emit_fn_body(fn);

    emit_epilogue();

    put(risc_v_ret());
}

/**********************************************
 **                Driver code               **
 **********************************************/
static uint64_t _entry_main_call_addr = 0x00;

static void emit_entry_fn()
{
    hashmap_init(&var_map, 512);

    put_sym("_start");
    _entry_main_call_addr = emitted_bytes;
    /* We don't know where `main` is located at this
       point of codegen. Now we occupy space with some
       senseless instruction.

       Will be replaced with
       \
        jal ra, <main_offset> */
    put(0);
    /* Ensure `a0` first parameter is occupied by some
       computation result */
    put(risc_v_xor(risc_v_reg_a0, risc_v_reg_a0,risc_v_reg_a0));
    put(risc_v_add(risc_v_reg_a0, risc_v_reg_a0, risc_v_reg_t0));
    put(risc_v_li(risc_v_reg_a7, __NR_exit));
    put(risc_v_ecall());
}

/**********************************************
 **                Driver code               **
 **********************************************/
void risc_v_gen(struct codegen_output *output, struct ir_unit *unit)
{
    codegen_output = output;
    emitted_bytes = 0;

    ir_reg_alloc(unit, __weak_array_size(allocatable_regs));
    ir_dump_unit(stdout, unit);
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
    replace(
        _entry_main_call_addr,
        risc_v_jal(risc_v_reg_ra, get_sym("main"))
    );

    hashmap_destroy(&fn_addr_map);
    hashmap_destroy(&var_map);
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
