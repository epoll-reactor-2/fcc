/* risc_v.c - RISC-V code generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v.h"
#include "back_end/risc_v_encode.h"
#include "middle_end/ir/ir.h"
#include "util/crc32.h"
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
    put_code(risc_v_li(risc_v_reg_a0, 123));
    put_code(risc_v_li(risc_v_reg_a7, __NR_exit));
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
