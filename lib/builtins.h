/* builtins.h - Embedded in language function prototypes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BUILTINS_H
#define WEAK_COMPILER_BUILTINS_H

#include "front_end/lex/data_type.h"
#include <stdint.h>

struct builtin_fn {
    char           name[64];
    enum data_type rt; /* Return value. */
    uint64_t       args_cnt;
    enum data_type args[16];
};

static struct builtin_fn builtin_fns[1] = {
    { "call_trace", D_T_VOID, 0, {} }
};

#endif // WEAK_COMPILER_BUILTINS_H