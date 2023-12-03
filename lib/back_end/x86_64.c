/* x86_64.c - x86_64 code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/x86_64.h"
#include "middle_end/ir/ir.h"
#include <stdarg.h>
#include <stdio.h>

static FILE *code_stream;

static void report(const char *msg)
{
    perror(msg);
    exit(1);
}

static void init()
{
    code_stream = tmpfile();
    if (!code_stream)
        report("tmpfile()");
}

static void reset()
{
    if (fclose(code_stream) < 0)
        report("fclose()");
}

fmt(1, 2) static void emit(const char *fmt, ...)
{
    va_list args;
    va_start(args, fmt);
    vfprintf(code_stream, fmt, args);
    va_end(args);
}

void x86_64_gen(struct ir_unit *unit)
{
    (void) unit;

    init();
    reset();
}