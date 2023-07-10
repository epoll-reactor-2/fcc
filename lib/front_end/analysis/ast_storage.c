/* ast_storage.с - Storage for declarations being AST nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/ast_storage.h"
#include "util/alloc.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include <assert.h>
#include <string.h>
#include <stdio.h>

static uint16_t scope_depth;
static hashmap_t scopes;

void ast_storage_init_state()
{
    scope_depth = 0;
    hashmap_init(&scopes, 100);
}

void ast_storage_reset_state()
{
    scope_depth = 0;
    hashmap_foreach(&scopes, key, val) {
        (void) key;
        struct ast_storage_decl *decl = (struct ast_storage_decl *) val;
        weak_free(decl);
    }
    hashmap_destroy(&scopes);
}

void ast_storage_start_scope()
{
    ++scope_depth;
}

void ast_storage_end_scope()
{
    hashmap_foreach(&scopes, key, val) {
        struct ast_storage_decl *decl = (struct ast_storage_decl *) val;
        if (decl->depth == scope_depth)
            hashmap_remove(&scopes, key);
    }
    --scope_depth;
}

void ast_storage_push(const char *var_name, struct ast_node *ast)
{
    ast_storage_push_typed(var_name, D_T_UNKNOWN, ast);
}

void ast_storage_push_typed(const char *var_name, enum data_type dt, struct ast_node *ast)
{
    struct ast_storage_decl *decl = weak_calloc(1, sizeof (struct ast_storage_decl));
    decl->ast = ast;
    decl->data_type = dt;
    decl->name = strdup(var_name);
    decl->read_uses = 0;
    decl->write_uses = 0;
    decl->depth = scope_depth;
    hashmap_put(&scopes, crc32_string(var_name), (uint64_t) decl);
}

struct ast_storage_decl *ast_storage_lookup(const char *var_name)
{
    uint64_t hash = crc32_string(var_name);
    bool ok = 0;
    int64_t addr = hashmap_get(&scopes, hash, &ok);

    if (!ok || addr == 0)
        return NULL;

    struct ast_storage_decl *decl = (struct ast_storage_decl *) addr;

    if (decl->depth > scope_depth)
        return NULL;

    return decl;
}

void ast_storage_add_read_use(const char *var_name)
{
    struct ast_storage_decl *decl = ast_storage_lookup(var_name);
    assert(decl && "Variable expected to be declared before");
    assert(decl->depth <= scope_depth && "Impossible case: variable depth >= current depth");
    decl->read_uses++;
}

void ast_storage_add_write_use(const char *var_name)
{
    struct ast_storage_decl *decl = ast_storage_lookup(var_name);
    assert(decl && "Variable expected to be declared before");
    assert(decl->depth <= scope_depth && "Impossible case: variable depth >= current depth");
    decl->write_uses++;
}

void ast_storage_current_scope_uses(ast_storage_decl_array_t *out_set)
{
    hashmap_foreach(&scopes, key, val) {
        (void) key;
        struct ast_storage_decl *decl = (struct ast_storage_decl *) val;
        if (decl->depth == scope_depth)
            vector_push_back(*out_set, decl);
    }
}
