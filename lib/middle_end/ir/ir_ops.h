/* ir_ops.h - Useful operations on IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_OPS_H
#define WEAK_COMPILER_MIDDLE_END_IR_OPS_H

#include "util/vector.h"
#include <stdbool.h>

struct ir_node;
typedef vector_t(struct ir_node *) ir_vector_t;

/** Remove `ir` from IR. If `ir` is a first statement
    in list, update `list_head`. */
void ir_remove(struct ir_node **ir, struct ir_node **list_head);

#endif // WEAK_COMPILER_MIDDLE_END_IR_OPS_H