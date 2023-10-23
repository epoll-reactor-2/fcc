/* meta.h - Extra information about IR nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_META_H
#define WEAK_COMPILER_MIDDLE_END_META_H

#include <stdint.h>
#include <stdbool.h>

struct meta {
    enum {
        IR_META_VAR,
        IR_META_FUN
    } type;

    union {
        /// Variable information.
        struct {
            bool    loop;
            bool    noalias;
            int32_t loop_idx;
        } sym_meta;

        /// Function information.
        struct {
            bool is_const;
        } fun_meta;
    };

    uint64_t loop_depth;
};

void *meta_init(int32_t type);
void  meta_cleanup(void *meta);

#endif // WEAK_COMPILER_MIDDLE_END_META_H