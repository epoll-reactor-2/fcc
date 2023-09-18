/* storage.h - Storage for intermediate code variables.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_IR_STORAGE_H
#define WEAK_COMPILER_MIDDLE_END_IR_STORAGE_H

#include "util/compiler.h"
#include <stdint.h>

/// This IR storage mapping variable name to its IR index.
///
/// Preconditions
///   1: Types are checked during analysis.
/// Operations
///   1: Push variable index (number) assicoated with its textual name (string).
///   2: Get variable index (number) by string.
///
/// \note
///   1: There is no scope separation as in front-end
///      AST storage, so it does not makes sence to do that
///      since each variable in IR is unique (incremental).

void ir_storage_init();
void ir_storage_reset();

struct ir_storage_record {
    int32_t         sym_idx;
    /// Allocated inside internal hashmap.
    /// Not needed to free.
    struct ir_node *ir;
};

void
ir_storage_push(const char *name, int32_t ir_idx, struct ir_node *ir);

__weak_wur struct ir_storage_record *
ir_storage_get (const char *name);

#endif // WEAK_COMPILER_MIDDLE_END_IR_STORAGE_H