/* io.c - Input-output utils.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/io.h"
#include "util/unreachable.h"
#include <stdarg.h>
#include <stdlib.h>

void system_read(char *out, const char *fmt, ...)
{
    char    buf [1024] = {0};
    char    cmd [1024] = {0};
    ssize_t written    =  0;

    va_list args;
    va_start(args, fmt);
    vsnprintf(cmd, sizeof(cmd), fmt, args);
    va_end(args);

    /* Open the cmd for reading. */
    FILE *fp = popen(cmd, "r");
    if (!fp)
        weak_fatal_errno("fopen()");

    while (fgets(buf, sizeof(buf), fp) != NULL)
        written += sprintf(out + written, "%s", buf);

    pclose(fp);
}

int system_run(const char *fmt, ...)
{
    char cmd[1024] = {0};

    va_list args;
    va_start(args, fmt);
    vsnprintf(cmd, sizeof(cmd), fmt, args);
    va_end(args);

    return system(cmd);
}