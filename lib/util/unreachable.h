/* unreachable.h - Missing return statement warning suppress.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTIL_UNREACHABLE_H
#define WEAK_COMPILER_UTIL_UNREACHABLE_H

#include "util/compiler.h"
#include <stdio.h>

#define weak_fatal_error(msg) do {                                        \
    printf("Fatal error ocurred at %s@%d: %s\n", __FILE__, __LINE__, (msg)); \
    fflush(stdout);                                                       \
    __builtin_trap();                                                     \
} while (0);

#define weak_unreachable(msg) do {                                        \
    printf("Unreachable point reached at %s@%d: %s\n", __FILE__, __LINE__, (msg));  \
    fflush(stdout);                                                       \
    __builtin_trap();                                                     \
} while (0);

#endif // WEAK_COMPILER_UTIL_UNREACHABLE_H