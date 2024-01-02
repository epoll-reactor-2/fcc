/* ast_storage.с - Storage for declarations being AST nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/ast_storage.h"
#include "util/alloc.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include <assert.h>
#include <string.h>

void ast_storage_init(struct ast_storage *s)
{
    s->scope_depth = 0;
    hashmap_init(&s->scopes, 8192 * 16);
}

void ast_storage_free(struct ast_storage *s)
{
    s->scope_depth = 0;
    hashmap_foreach(&s->scopes, k, v) {
        (void) k;
        weak_free((void *) v);
    }
    hashmap_destroy(&s->scopes);
}

void ast_storage_start_scope(struct ast_storage *s)
{
    ++s->scope_depth;
}

void ast_storage_end_scope(struct ast_storage *s)
{
    hashmap_foreach(&s->scopes, k, v) {
        struct ast_storage_decl *decl = (struct ast_storage_decl *) v;
        if (decl->depth == s->scope_depth) {
            weak_free(decl);
            hashmap_remove(&s->scopes, k);
        }
    }
    --s->scope_depth;
}

void ast_storage_push(struct ast_storage *s, const char *var_name, struct ast_node *ast)
{
    ast_storage_push_typed(s, var_name, D_T_UNKNOWN, /*ptr_depth=*/0, ast);
}

void ast_storage_push_typed(
    struct ast_storage *s,
    const char         *var_name,
    enum data_type      dt,
    uint16_t            ptr_depth,
    struct ast_node    *ast
) {
    struct ast_storage_decl *decl = weak_calloc(1, sizeof (struct ast_storage_decl));
    decl->ast = ast;
    decl->data_type = dt;
    decl->name = var_name;
    decl->ptr_depth = ptr_depth;
    decl->read_uses = 0;
    decl->write_uses = 0;
    decl->depth = s->scope_depth;
    hashmap_put(&s->scopes, crc32_string(var_name), (uint64_t) decl);
}

struct ast_storage_decl *ast_storage_lookup(struct ast_storage *s, const char *var_name)
{
    uint64_t hash = crc32_string(var_name);
    bool ok       = 0;
    int64_t addr  = hashmap_get(&s->scopes, hash, &ok);

    if (!ok || addr == 0)
        return NULL;

    struct ast_storage_decl *decl = (struct ast_storage_decl *) addr;

    if (decl->depth > s->scope_depth)
        return NULL;

    return decl;
}

void ast_storage_add_read_use(struct ast_storage *s, const char *var_name)
{
    struct ast_storage_decl *decl = ast_storage_lookup(s, var_name);
    assert(decl && "Variable expected to be declared before");
    assert(decl->depth <= s->scope_depth && "Impossible case: variable depth > current depth");
    decl->read_uses++;
}

void ast_storage_add_write_use(struct ast_storage *s, const char *var_name)
{
    struct ast_storage_decl *decl = ast_storage_lookup(s, var_name);
    assert(decl && "Variable expected to be declared before");
    assert(decl->depth <= s->scope_depth && "Impossible case: variable depth > current depth");
    decl->write_uses++;
}

void ast_storage_current_scope_uses(struct ast_storage *s, ast_storage_decl_array_t *out_set)
{
    hashmap_foreach(&s->scopes, k, v) {
        (void) k;
        struct ast_storage_decl *decl = (struct ast_storage_decl *) v;
        if (decl->depth == s->scope_depth)
            vector_push_back(*out_set, decl);
    }
}
