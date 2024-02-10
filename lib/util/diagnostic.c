/* diagnostic.c - Diagnostics engine.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/diagnostic.h"
#include "util/lexical.h"
#include "util/compiler.h"
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

jmp_buf weak_fatal_error_buf;

extern void *diag_error_memstream;
extern void *diag_warn_memstream;

static const char *active_filename;
static FILE       *active_stream;

static struct diag_config config = {
    .ignore_warns  = 1,
    .show_location = 0
};

void weak_diag_set_config(struct diag_config *new_config)
{
    memcpy(&config, new_config, sizeof (config));
}

void weak_set_source_filename(const char *filename)
{
    active_filename = filename;
}

void weak_set_source_stream(FILE *stream)
{
    active_stream = stream;
}

static noreturn void weak_terminate_compilation()
{
    longjmp(weak_fatal_error_buf, 1);
    __builtin_trap(); /* Just to be sure that we will never get there. */
}



really_inline static void replace_newline(char *buf)
{
    while (*buf) {
        if (*buf == '\n')
            *buf = ' ';
        ++buf;
    }
}

static void flush(char *buf, bool is_error)
{
    FILE *out_stream = is_error
        ? diag_error_memstream
        : diag_warn_memstream;

    fputs(buf, out_stream);
    fflush(out_stream);
}

/* There is warning
    | warning: ' ' flag used with ‘%u’ gnu_printf format [-Wformat=]
   "| % 6lu: %s\n"
   ^~~~~~~~~~~~~~~

   After some research we know, that this issue is implementation detail
   of printf() when printing unsigned values. This behaviour can differ
   on Linux and other POSIX systems. I use Linux, so I don't care.
   */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wformat"
unused static void print_file_range(
    FILE     *stream,
    uint64_t  line_no,
    uint64_t  col_no,
    char     *err_buf,
    uint64_t  range,
    bool      is_error
) {
    fseek(stream, 0, SEEK_SET);

    uint64_t curr_line_no =  1;
    char     buf[4096]    = {0};

    for (uint64_t i = 1; i < line_no - range && fgets(buf, sizeof (buf), active_stream) != NULL; ++i)
        ++curr_line_no;

    fputs("", stream);

    char     report[65536] = {0};
    uint64_t w             =  0;
    uint64_t line_max      =  0;

    char *msg_color = is_error ? color_red : color_yellow;
    char *line_color = color_purple;

#define DO() \
        { replace_newline(buf); \
          uint64_t written = sprintf(report + w, "%s|%s %s% 6lu:%s %s\n", msg_color, color_end, line_color, curr_line_no++, color_end, buf); \
          \
          if (line_max < strlen(buf) + 7) \
              line_max = strlen(buf) + 7; \
          \
          w += written; }

#define GET() fgets(buf, sizeof (buf), stream)

    /* Before. */
    for (uint64_t i = range > line_no
                    ? 0
                    : line_no - range;  i < line_no && GET() != NULL; ++i)
        DO()

    /* Error/warning line. */
    for (uint64_t i = line_no; i <= line_no && GET() != NULL; ++i) {
        DO()

        w += sprintf(report + w, "%s|%s        %-*s%s^%s\n", msg_color, color_end, (int) col_no, " ", msg_color, color_end);
        w += sprintf(report + w, "%s|        %s%s\n", msg_color, err_buf, color_end);
        w += sprintf(report + w, "%s|%s\n", msg_color, color_end);
    }

    /* After. */
    for (uint64_t i = line_no + 1; i <= line_no + range && GET() != NULL; ++i)
        DO()

    flush(report, is_error);

#undef GET
#undef DO
}
#pragma GCC diagnostic pop /* -Wformat */



void weak_compile_error(uint16_t line_no, uint16_t col_no, const char *fmt, ...)
{
    FILE *stream = diag_error_memstream != NULL
        ? diag_error_memstream
        : stderr;

    va_list args;

    if (!config.show_location) {
        fprintf(stream, "%s: E<%u:%u>: ", active_filename, line_no, col_no);

        va_start(args, fmt);
        vfprintf(stream, fmt, args);
        va_end(args);
    }

    char buf[8192] = {0};

    va_start(args, fmt);
    vsprintf(buf, fmt, args);
    va_end(args);

    if (config.show_location)
        print_file_range(active_stream, line_no, col_no, buf, 3, /*is_error=*/1);

    fputc('\n', stream);
    fflush(stream);

    weak_terminate_compilation();
}

void weak_compile_warn(uint16_t line_no, uint16_t col_no, const char *fmt, ...)
{
    if (config.ignore_warns)
        return;

    FILE *stream = diag_warn_memstream != NULL
        ? diag_warn_memstream
        : stderr;

    va_list args;

    if (!config.show_location) {
        fprintf(stream, "%s: W<%u:%u>: ", active_filename, line_no, col_no);

        va_start(args, fmt);
        vfprintf(stream, fmt, args);
        va_end(args);
    }

    char buf[8192] = {0};

    va_start(args, fmt);
    vsprintf(buf, fmt, args);
    va_end(args);

    if (config.show_location)
        print_file_range(active_stream, line_no, col_no, buf, 3, /*is_error=*/0);

    fputc('\n', stream);
    fflush(stream);
}
