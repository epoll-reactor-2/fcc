/* risc_v.h - RISC-V code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_RISC_V_H
#define WEAK_COMPILER_BACKEND_RISC_V_H

#include <bits/types/FILE.h>

struct ir_unit;

void risc_v_gen(FILE *stream, struct ir_unit *unit);

#endif // WEAK_COMPILER_BACKEND_RISC_V_H