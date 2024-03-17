/* meta.h - Extra information about IR nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef FCC_MIDDLE_END_META_H
#define FCC_MIDDLE_END_META_H

#include "front_end/data_type.h"
#include <stdint.h>
#include <stdbool.h>

enum { META_VALUE_UNKNOWN = UINT64_MAX };

struct meta {
    enum {
        IR_META_UNKNOWN = 0,
        IR_META_SYM     = 2,
        IR_META_FUN     = 4
    } kind;

    union {
        /** Variable information. */
        struct {
            bool    loop;
            bool    noalias;
            int32_t loop_idx;
        } sym;

        /** Function information. */
        struct {
            bool is_const;
        } fun;
    };

    /** Depth of current block. Needed to handle
        nested code blocks inside '{' and '}' in optimizations. */
    uint64_t block_depth;

    /** Most outer loop index. Needed to know when
        to stop optimizing algorithms in case when
        loops are placed close. Without it
        we could incorrectly think, that shown below
        3 while's is the same loop because of same
        loop depth.

        while (a) { ... } /< Loop depth = 1
        <<< separator >>>

        while (b) { ... } /< Loop depth = 1
        <<< separator >>>

        while (c) { ... } /< Loop depth = 1
        <<< separator >>> */
    uint64_t global_loop_idx;
};

#endif // FCC_MIDDLE_END_META_H
