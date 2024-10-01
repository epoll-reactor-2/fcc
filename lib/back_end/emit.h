/* emit.h - Code generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_EMIT_H
#define WEAK_COMPILER_BACKEND_EMIT_H

#include "back_end/elf.h"

struct ir_unit;

void back_end_gen(struct ir_unit *unit);

#endif // WEAK_COMPILER_BACKEND_EMIT_H