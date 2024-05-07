/* const.h - Constant AST analyzer and interpreter.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_CONST_H
#define WEAK_COMPILER_FRONTEND_CONST_H

#include <stdbool.h>
#include <stdio.h>

struct ast_node;
/* This file should be used by dead_ana.c. This
   encapsulates checks for AST node constant property. */
void const_init();
/* Clear the mapping for current translation unit. */
void const_reset();
void const_start_scope();
void const_end_scope();

/* Try to evaluate declaration body and add to const
   mapping. */
void const_try_store(struct ast_node *ast);

bool is_const_evaluable(struct ast_node *ast);

void const_statistics(FILE *stream);

#endif /* WEAK_COMPILER_FRONTEND_CONST_H */
