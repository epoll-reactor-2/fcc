/* io.h - Input-output utils.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTIL_IO_H
#define WEAK_COMPILER_UTIL_IO_H

#include <stdio.h>

void system_read(char *out, const char *fmt, ...);
int  system_run(const char *fmt, ...);

#endif // WEAK_COMPILER_UTIL_IO_H