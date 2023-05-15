/* code_gen.h - Code generation entry point.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_BACKEND_CODE_GEN_H
#define WEAK_COMPILER_BACKEND_CODE_GEN_H

typedef struct ast_node_t ast_node_t;

void code_gen(ast_node_t *root);

#endif // WEAK_COMPILER_BACKEND_CODE_GEN_H