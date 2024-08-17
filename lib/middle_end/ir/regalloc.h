/* regalloc.h - Register allocator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_REGALLOC_H
#define WEAK_COMPILER_MIDDLE_REGALLOC_H

struct ir_node;

void ir_reg_alloc(struct ir_node *functions);

#endif // WEAK_COMPILER_MIDDLE_REGALLOC_H