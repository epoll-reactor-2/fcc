/* type.h - IR pass that adds type information.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TYPE_H
#define WEAK_COMPILER_MIDDLE_END_TYPE_H

#include "front_end/lex/data_type.h"
#include <stdint.h>

struct ir_unit;

struct type {
    enum data_type dt;
    uint64_t       ptr_depth;
    uint64_t       arity[16];
    uint64_t       arity_size;
    uint64_t       bytes;
};

/** Supply each expression with its type
    information.

    Expressions:
    - ir_sym
    - ir_imm
    - ir_fn_call
    - ir_member (TODO: implement) */
void ir_type_pass(struct ir_unit *unit);

uint64_t ir_type_size(enum data_type dt);

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_H