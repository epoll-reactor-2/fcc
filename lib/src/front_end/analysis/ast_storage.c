/* ast_storage.с - Storage for declarations being AST nodes.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/ast_storage.h"
#include "utility/crc32.h"
#include "utility/hashmap.h"
#include <assert.h>
#include <string.h>

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
    hashmap_clear(&scopes);
}

void ast_storage_start_scope()
{
    ++scope_depth;
}

void ast_storage_end_scope()
{
    hashmap_foreach(&scopes, key, val) {
        ast_storage_decl_t *decl = (ast_storage_decl_t *)val;
        if (decl->depth == scope_depth)
            hashmap_remove(&scopes, key);
    }
    --scope_depth;
}

void ast_storage_push(const char *var_name, ast_node_t *ast)
{
    ast_storage_push_typed(var_name, D_T_UNKNOWN, ast);
}

void ast_storage_push_typed(const char *var_name, data_type_e dt, ast_node_t *ast)
{
    ast_storage_decl_t decl = {
        .ast = ast,
        .data_type = dt,
        .name = strdup(var_name),
        .read_uses = 0,
        .write_uses = 0,
        .depth = scope_depth,
    };
    hashmap_put(&scopes, (size_t)crc32_string(var_name), (size_t)&decl);
}



ast_storage_decl_t *ast_storage_lookup(const char *var_name)
{
    size_t hash = crc32_string(var_name);
    size_t addr = hashmap_get(&scopes, hash);

    if (addr == 0)
        return NULL;

    ast_storage_decl_t *decl = (ast_storage_decl_t *)addr;

    if (decl->depth > scope_depth)
        return NULL;

    return decl;
}

void ast_storage_add_read_use(const char *var_name)
{
    ast_storage_decl_t *decl = ast_storage_lookup(var_name);
    assert(decl && "Variable expected to be declared before");
    assert(decl->depth <= scope_depth && "Impossible case: variable depth >= current depth");
    decl->read_uses++;
}

void ast_storage_add_write_use(const char *var_name)
{
    ast_storage_decl_t *decl = ast_storage_lookup(var_name);
    assert(decl && "Variable expected to be declared before");
    assert(decl->depth <= scope_depth && "Impossible case: variable depth >= current depth");
    decl->write_uses++;
}