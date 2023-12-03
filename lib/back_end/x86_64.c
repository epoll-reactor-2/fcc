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