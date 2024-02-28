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