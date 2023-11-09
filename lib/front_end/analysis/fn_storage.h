/* fn_storage.h - Storage for function declarations.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_FN_STORAGE_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_FN_STORAGE_H

#include "util/hashmap.h"

struct ast_function_decl;
struct builtin_fn;

/** - Key:   CRC-32 of function name.
    - Value: Pointer to malloc()'ed struct builtin.

   \note Storages for AST and functions are different
         because of bit different semantics. */
typedef hashmap_t fn_storage_t;

void fn_storage_init(fn_storage_t *s);
void fn_storage_free(fn_storage_t *s);

void fn_storage_push(
    fn_storage_t             *s,
    const char               *name,
    struct ast_function_decl *decl
);

struct builtin_fn *fn_storage_lookup(
    fn_storage_t *s,
    const char   *name
);

#endif //WEAK_COMPILER_FRONTEND_ANALYSIS_FN_STORAGE_H