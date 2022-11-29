/* Unreachable.h - Missing return statement warning suppress.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

extern "C" int printf(const char *__restrict fmt, ...);

#define Unreachable() \
  { \
    printf("Unreachable point reached at %s:L%d", __FILE__, __LINE__); \
    __builtin_trap();  \
  }