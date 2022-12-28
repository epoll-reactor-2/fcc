/* unreachable.h - Missing return statement warning suppress.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_UNREACHABLE_H
#define WEAK_COMPILER_UTILITY_UNREACHABLE_H

#include "utility/compiler.h"

extern int printf(const char *__restrict fmt, ...);

#define weak_fatal_error(msg) \
  { \
    printf("Fatal error ocurred at %s: %s\n", SOURCE_LINE, (msg)); \
    __builtin_trap();  \
  }

#define weak_unreachable(msg) \
  { \
    printf("Unreachable point reached at %s: %s\n", SOURCE_LINE, (msg)); \
    __builtin_trap();  \
  }

#endif // WEAK_COMPILER_UTILITY_UNREACHABLE_H