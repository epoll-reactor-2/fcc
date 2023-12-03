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

/* ==========================
   Printers.
   ========================== */

static FILE *code_stream;

static void report(const char *msg)
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

/* ==========================
   Register selection routines.
   ========================== */

static const char *cdecl_reg(int arg_idx)
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

struct x86_64_reg {
    const char *reg;
    bool        free;
};

/* TODO: Mapping IR variables to registers/stack location. */
static struct x86_64_reg regs[] = {
    { "rax", 1 },
    { "rdi", 1 },
    { "rsi", 1 },
    { "rdx", 1 },
    { "r8",  1 },
    { "r9",  1 },
    { "r10", 1 },
    { "r11", 1 },
    { "r12", 1 },
    { "r13", 1 },
    { "r14", 1 },
    { "r15", 1 },
};

/* ==========================
   Code generation routines.
   ========================== */

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
        emit(
            "\tpush\trbp\n"
            "\tmov\trbp, rsp\n"
        );
    /* Body. */
    /* ... */
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
        emit(
            "\tmov\trsp, rbp\n"
            "\tpop\trbp\n"
            "\tret\n"
        );
}

static void emit_header()
{
    emit(
        "section .text\n"
        "\tglobal\t_start\n"
    );
}

/* ==========================
   Driver code.
   ========================== */

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
Может вовсе не он был худохник
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