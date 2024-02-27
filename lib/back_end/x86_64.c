/* x86_64.c - x86_64 code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/x86_64.h"
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

fmt(1, 2) static void emit(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    vfprintf(code_stream, fmt, args);
    va_end(args);
}

/**********************************************
 **        Register selection routines       **
 **********************************************/
unused static const char *cdecl_reg(int arg_idx)
{
    switch (arg_idx) {
    case 0:  return "rdi";
    case 1:  return "rsi";
    case 2:  return "rdx";
    case 3:  return "r10";
    case 4:  return "r8";
    case 5:  return "r9";
    default: return NULL; /* Shall push. */
    }
}

static const char *ptr_suffix(uint64_t size)
{
    switch (size) {
    case 1: return "byte";
    case 2: return "word";
    case 4: return "dword";
    case 8: return "qword";
    default:
        weak_fatal_error("Invalid size: %ld", size);
    }
}

struct x86_64_reg {
    const char *reg;
    bool        free;
};

/**********************************************
 **        Code generation routines          **
 **********************************************/
static void emit_alloca(struct ir_alloca *ir)
{
    (void) ir;
}

static void emit_alloca_array(struct ir_alloca_array *ir)
{
    (void) ir;
}

static void emit_imm(struct ir_imm *ir)
{
    (void) ir;
}

static void emit_sym(struct ir_sym *ir)
{
    (void) ir;
}

static void emit_store(struct ir_store *ir)
{
    (void) ir;
    /* Calculate everything using EAX/RAX, store by
       stack offset or register (variable map => stack offset). */
}

static void emit_bin(struct ir_bin *ir)
{
    (void) ir;
}

static void emit_jump(struct ir_jump *ir)
{
    (void) ir;
}

static void emit_cond(struct ir_cond *ir)
{
    (void) ir;
}

static void emit_ret(struct ir_ret *ir)
{
    (void) ir;
}

static void emit_fn_call(struct ir_fn_call *ir)
{
    (void) ir;
    /* 1. If cdecl registers are busy, push them.
       2. Move arguments according to cdecl.
       3. Pop registers back.
       4. Return value stored in RAX? */
}

static void emit_phi(struct ir_phi *ir)
{
    (void) ir;
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

static const char *cdecl_regs[] = {
    "rax",
    "rdi",
    "rsi",
    "rdx",
    "r10",
    "r8",
    "r9",
    NULL
};

/*
#include <stdint.h>

int f(char a1, signed a2, int a3, int a4, int a5,
      int  a6, int    a7, int a8, int a9, int a10, int a11) {
    return a3 + a4 + a6 + a7 + a11;
}

f(char, int, int, int, int, int, int, int, int, int, int):
        push    rbp
        mov     rbp, rsp
        mov     al, dil
        mov     edi, dword ptr [rbp + 48]
        mov     edi, dword ptr [rbp + 40]
        mov     edi, dword ptr [rbp + 32]
        mov     edi, dword ptr [rbp + 24]
        mov     edi, dword ptr [rbp + 16]
        mov     byte ptr [rbp - 1], al
        mov     dword ptr [rbp - 8], esi
        mov     dword ptr [rbp - 12], edx
        mov     dword ptr [rbp - 16], ecx
        mov     dword ptr [rbp - 20], r8d
        mov     dword ptr [rbp - 24], r9d
        mov     eax, dword ptr [rbp - 12]
        add     eax, dword ptr [rbp - 16]
        add     eax, dword ptr [rbp - 24]
        add     eax, dword ptr [rbp + 16]
        add     eax, dword ptr [rbp + 48]
        pop     rbp
        ret
*/

static void emit_fn_args(struct ir_fn_decl *decl)
{
    struct ir_node *it         = decl->args;
    /* TODO: Should be global for function (args, body). */
    uint64_t        stack_off  = 0;
    uint64_t        arg_num    = 0;
    uint64_t        total_regs = __weak_array_size(cdecl_regs);

    while (it) {
        struct ir_alloca *alloca = it->ir;

        uint64_t    size = ir_type_size(alloca->dt);
        const char *reg  = cdecl_regs[arg_num++];

        if (arg_num < total_regs)
            emit(
                "\tmov\t[rbp - %ld], %s\n",
                stack_off,
                reg
            );
        else
            /* Take rest of args from stack. */
            // emit("\tpush...\n");
            ;
        stack_off += size;
        it = it->next;
    }
}

static void emit_fn_body(struct ir_node *ir)
{
    while (ir) {
        emit_instr(ir);
        ir = ir->next;
    }
}

static void emit_prologue()
{
    emit(
        "\tpush\trbp\n"
        "\tmov\trbp, rsp\n"
    );
}

static void emit_epilogue()
{
    emit(
        "\tmov\trsp, rbp\n"
        "\tpop\trbp\n"
        "\tret\n"
    );
}

static void emit_fn(struct ir_fn_decl *fn)
{
    char *name = fn->name;
    bool  main = !strcmp(name, "main");
    if (main)
        emit("_start:\n");
    else
        emit("%s:\n", name);
    /* Prologue (cdecl). Not required in _start. */
    if (!main)
        emit_prologue();
    emit_fn_args(fn);
    /* Body. */
    emit_fn_body(fn->body);
    /* Epilogue (cdecl). Not required in _start. */
    if (main)
        emit(
            "\tmov\trax, %d\n"
            "\tmov\trdi, %d\n"
            "\tsyscall\n",
            __NR_exit,
            /* TODO: Exit value. */ 0
        );
    else
        emit_epilogue();
}

static void emit_header()
{
    emit(
        "section .text\n"
        "\tglobal\t_start\n"
    );
}

/**********************************************
 **                Driver code               **
 **********************************************/
void x86_64_gen(FILE *stream, struct ir_unit *unit)
{
    (void) unit;

    code_stream = stream;

    puts("");
    emit_header();

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