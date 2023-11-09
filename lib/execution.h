/* execution.h - Common evaluation result type.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_EXECUTION_H
#define WEAK_COMPILER_EXECUTION_H

#include "front_end/lex/data_type.h"
#include <stdint.h>

/* This structure is moved out from
   front-, middle-, or back-end, since
   represents value that function can
   potentially return. */
struct value {
    enum data_type dt;

    union {
        bool    __bool;
        char    __char;
        int32_t __int;
        float   __float;
        struct {
            uint64_t  siz;
            char     *value;
        } __string;
        struct {
            /* TODO. */
        } __struct;
    };
};

#endif // WEAK_COMPILER_EXECUTION_H