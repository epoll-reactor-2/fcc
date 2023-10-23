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

    /// Depth of current loop. Needed to handle
    /// nested loops in optimizations.
    uint64_t loop_depth;

    /// Most outer loop index. Needed to know when
    /// to stop optimizing algorithms in case when
    /// loops are placed close. Without it
    /// we could incorrectly think, that shown below
    /// 3 while's is the same loop because of same
    /// loop depth.
    ///
    /// while (a) { ... } /< Loop depth = 1
    /// <<< separator >>>
    ///
    /// while (b) { ... } /< Loop depth = 1
    /// <<< separator >>>
    ///
    /// while (c) { ... } /< Loop depth = 1
    /// <<< separator >>>
    uint64_t global_loop_idx;
};

void *meta_init(int32_t type);
void  meta_cleanup(void *meta);

#endif // WEAK_COMPILER_MIDDLE_END_META_H