/* ssa.h - Static single assignment routines.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_SSA_H
#define WEAK_COMPILER_MIDDLE_END_SSA_H

#include <stdint.h>
#include <stdbool.h>

struct ir_node;

void ir_compute_ssa(struct ir_node *functions);

#endif // WEAK_COMPILER_MIDDLE_END_SSA_H