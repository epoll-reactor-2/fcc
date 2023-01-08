/* diagnostic.c - Diagnostics engine.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "utility/diagnostic.h"
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

jmp_buf weak_fatal_error_buf;

extern void *diag_error_memstream;
extern void *diag_warn_memstream;

static noreturn void weak_terminate_compilation()
{
    longjmp(weak_fatal_error_buf, 1);
    __builtin_trap(); /// Just to be sure that we will never get there.
}

void weak_compile_error(uint16_t line_no, uint16_t col_no, const char *fmt, ...)
{
    bool should_terminate = diag_error_memstream == NULL;

    FILE *stream = !should_terminate
        ? diag_error_memstream
        : stderr;

    fprintf(stream, "Error at line %u, column %u: ", line_no, col_no);

    va_list args;
    va_start(args, fmt);
    vfprintf(stream, fmt, args);
    va_end(args);

    fputc('\n', stream);
    fflush(stream);

    if (should_terminate) {
        abort();
    }

    weak_terminate_compilation();
}

void weak_compile_warn(uint16_t line_no, uint16_t col_no, const char *fmt, ...)
{
    FILE *stream = diag_warn_memstream
        ? diag_warn_memstream
        : stderr;

    fprintf(stream, "Warning at line %u, column %u: ", line_no, col_no);

    va_list args;
    va_start(args, fmt);
    vfprintf(stream, fmt, args);
    va_end(args);

    fputc('\n', stream);
    fflush(stream);
}