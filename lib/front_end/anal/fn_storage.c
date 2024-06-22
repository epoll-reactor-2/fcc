/* fn_storage.c - Storage for function declarations.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/anal/fn_storage.h"
#include "front_end/ast/ast.h"
#include "util/alloc.h"
#include "util/crc32.h"
#include "builtins.h"
#include <string.h>

void fn_storage_init(fn_storage_t *s)
{
    hashmap_reset(s, 512);
}

void fn_storage_free(fn_storage_t *s)
{
    hashmap_foreach(s, k, v) {
        (void) k;
        struct builtin_fn *fn = (struct builtin_fn *) v;
        weak_free(fn);
    }
    hashmap_destroy(s);
}

void fn_storage_push(
    fn_storage_t       *s,
    const char         *name,
    struct ast_fn_decl *decl
) {
    struct builtin_fn   *fn   = weak_calloc(1, sizeof (struct builtin_fn));
    struct ast_compound *args = decl->args->ast;

    strncpy(fn->name, decl->name, sizeof (fn->name) - 1);
    fn->rt = decl->data_type;
    fn->args_cnt = args->size;

    for (uint16_t i = 0; i < fn->args_cnt; ++i) {
        struct ast_var_decl *arg = args->stmts[i]->ast;
        fn->args[i] = arg->dt;
    }

    hashmap_put(s, crc32_string(name), (uint64_t) fn);

}



static inline struct builtin_fn *fn_builtin_lookup(const char *name)
{
    for (uint64_t i = 0; i < __weak_array_size(builtin_fns); ++i)
         if (strcmp(builtin_fns[i].name, name) == 0)
            return &builtin_fns[i];

    return NULL;
}

struct builtin_fn *fn_storage_lookup(
    fn_storage_t *s,
    const char   *name
) {
    uint64_t hash = crc32_string(name);
    bool     ok   = 0;
    uint64_t addr = hashmap_get(s, hash, &ok);

    if (!ok || addr == 0)
        return fn_builtin_lookup(name);

    return (struct builtin_fn *) addr;
}