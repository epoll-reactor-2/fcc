/* type.h - IR pass that adds type information.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TYPE_H
#define WEAK_COMPILER_MIDDLE_END_TYPE_H

struct ir_unit;

/* Traverse IR and supply meta information of
   each symbol with all possible type traits. */
void ir_type_pass(struct ir_unit *unit);

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_H