/* regalloc.h - Register allocator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_REGALLOC_H
#define WEAK_COMPILER_MIDDLE_REGALLOC_H

#include <stdint.h>

struct ir_unit;

/** Perform register allocation.

    Graph-coloring algorithm is used.

    \param virtual_regs   Number of avaialble hardware registers. */
void ir_reg_alloc(struct ir_unit *unit, uint64_t hardware_regs);

#endif // WEAK_COMPILER_MIDDLE_REGALLOC_H