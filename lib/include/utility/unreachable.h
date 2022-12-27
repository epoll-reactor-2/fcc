/* unreachable.h - Missing return statement warning suppress.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

extern int printf(const char *__restrict fmt, ...);

#define weak_unreachable(msg) \
  { \
    printf("Unreachable point reached at %s:L%d: %s\n", __FILE__, __LINE__, msg); \
    __builtin_trap();  \
  }
