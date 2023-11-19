/* type.h - IR pass that adds type information.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TYPE_H
#define WEAK_COMPILER_MIDDLE_END_TYPE_H

struct ir_unit;

/** Supply each expression with its type
    information.

    Expressions:
    - ir_sym
    - ir_imm
    - ir_fn_call
    - ir_member (TODO: implement) */
void ir_type_pass(struct ir_unit *unit);

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_H