/* code_gen.h - Code generation entry point.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_CODE_GEN_H
#define WEAK_COMPILER_BACKEND_CODE_GEN_H

typedef struct ir_t ir_t;

void code_gen(ir_t *ir);

#endif // WEAK_COMPILER_BACKEND_CODE_GEN_H