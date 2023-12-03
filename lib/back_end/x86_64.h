/* x86_64.h - x86_64 code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_X86_64_H
#define WEAK_COMPILER_BACKEND_X86_64_H

struct ir_unit;

void x86_64_gen(struct ir_unit *unit);

#endif // WEAK_COMPILER_BACKEND_X86_64_H