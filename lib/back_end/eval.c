/* eval.c - Weak language IR interpreter.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/eval.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/dump.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include "util/vector.h"
#include "util/unreachable.h"
#include <assert.h>
#include <string.h>

static void reset_hashmap(hashmap_t *map)
{
    if (map->buckets) {
        hashmap_destroy(map);
    }
    hashmap_init(map, 512);
}



static vector_t(hashmap_t *) storages;

static void storage_new()
{
    hashmap_t *map = weak_calloc(1, sizeof (hashmap_t));
    hashmap_init(map, 128);
    vector_push_back(storages, map);
    __weak_debug_msg("Allocated storage, count: %ld\n", storages.count);
}

hashmap_t *storage_top()
{
    assert(storages.count > 0 && "Cannot get anything from empty storage.");
    return vector_back(storages);
}

void storage_pop()
{
    vector_erase(storages, storages.count - 1);
    __weak_debug_msg("Removed storage, count: %ld\n", storages.count);
}



static void eval_func_call(struct ir_func_call *fcall);

static void eval_store(struct ir_store *store)
{
    switch (store->type) {
    case IR_STORE_IMM:
    case IR_STORE_SYM:
    case IR_STORE_BIN:
        break;
    case IR_STORE_CALL: {
        struct ir_func_call *fcall = store->body->ir;
        eval_func_call(fcall);
        break;
    }
    default:
        break;
    }
}



static void eval_instr(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        break;
    case IR_IMM:
        break;
    case IR_SYM:
        break;
    case IR_LABEL:
        break;
    case IR_JUMP:
        break;
    case IR_MEMBER:
    case IR_ARRAY_ACCESS:
    case IR_TYPE_DECL:
        break;
    case IR_FUNC_DECL:
        break;
    case IR_FUNC_CALL:
        break;
    case IR_STORE:
        eval_store(ir->ir);
        break;
    case IR_BIN:
        break;
    case IR_RET:
    case IR_RET_VOID:
        break;
    case IR_COND:
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}



static hashmap_t function_list;

static struct ir_func_decl *function_list_lookup(const char *name)
{
    uint64_t hash = crc32_string(name);

    bool ok = 0;
    uint64_t got = hashmap_get(&function_list, hash, &ok);
    if (!ok)
        weak_unreachable("Cannot get function pointer `%s`", name);

    return (struct ir_func_decl *) got;
}



static void eval_func_decl(struct ir_func_decl *func)
{
    struct ir_node *it = func->body;
    while (it) {
        eval_instr(it);
        it = it->next;
    }
}

/// Preconditions:
/// 1) Allocated storage
/// 2) Computed and pushed to it arguments
static void call(const char *name)
{
    __weak_debug_msg("Calling `%s`\n", name);

    /// There should we eval arguments of ir_func_call.

    struct ir_func_decl *func = function_list_lookup(name);
    eval_func_decl(func);
}

static void eval_func_call(struct ir_func_call *fcall)
{
    storage_new();

    struct ir_node *it = fcall->args;
    while (it) {
        eval_instr(it);
        it = it->next;
    }

    call(fcall->name);

    storage_pop();
}



int32_t eval(struct ir_node *ir)
{
    reset_hashmap(&function_list);

    struct ir_node *it = ir;

    while (it) {
        struct ir_func_decl *func = it->ir;
        hashmap_put(&function_list, crc32_string(func->name), (uint64_t) func);
        it = it->next;
    }

    hashmap_foreach(&function_list, k, v) {
        struct ir_func_decl *func = (struct ir_func_decl *) v;
        __weak_debug_msg("Function in list: `%s`\n", func->name);
    }

    /// Allocate storage there manually. Allocated also
    /// in eval_func_call().
    storage_new();
    call("main");
    storage_pop();

    /// 1) Call main()
    ///
    ///    - storage = {}
    ///    - evaluate each IR node in main()
    ///    - return from eval()
    ///    - delete storage
    ///
    /// 2) call f(int a) inside main()
    ///
    ///    - save current jump target (-> points to function call of f())
    ///    - current function is main()
    ///    - create new storage = {}
    ///    - evaluate each f() argument
    ///    -   evaluate a -> $1 or $2, ...
    ///    -   evaluate each IR node in f()
    ///    -   \
    ///    -    with created new storage, that
    ///         have own variable indices (%0, %1, %...)
    ///
    ///    - delete created storage
    ///    - restore jump target
    ///      \
    ///       now it should point to next statement after call

    return 0;
}