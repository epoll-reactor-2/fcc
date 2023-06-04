/* code_gen.h - Code generation entry point.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_CODE_GEN_H
#define WEAK_COMPILER_BACKEND_CODE_GEN_H

struct ir;

void code_gen(struct ir *ir);

#endif // WEAK_COMPILER_BACKEND_CODE_GEN_H