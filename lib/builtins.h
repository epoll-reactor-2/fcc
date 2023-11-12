/* builtins.h - Embedded in language function prototypes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BUILTINS_H
#define WEAK_COMPILER_BUILTINS_H

#include "execution.h"

typedef struct value (*builtin_fn_t)(
    struct value */* args*/,
    uint64_t      /* args_cnt */);

struct builtin_fn {
    char           name[64];
    enum data_type rt; /* Return value. */
    uint64_t       args_cnt;
    enum data_type args[16];
    builtin_fn_t   fn;
};

/* There are two planned sources from where builtins may come
   - Embedded in language functions, written in C.
     They are statically stored in array below. And there
     should be as few as possible functions to ease maintaining.
     I plan:
       1) syscall wrappers
       2) some language-specific stuff like stack trace.

   - Functions, written in weak language and compiled to weak IR.
     They are written in weak language files, compiled and inserted to
     function list (struct ir_node * of function declarators)
     before starting evaluation.

     { precompiled_1, precompiled_2, from_source_1, from_source_2 } */
__weak_unused static struct builtin_fn builtin_fns[1] = {
    { "call_trace", D_T_VOID, 0, {}, /* TODO: write C builtins and pin pointer. */NULL }
};

#endif // WEAK_COMPILER_BUILTINS_H