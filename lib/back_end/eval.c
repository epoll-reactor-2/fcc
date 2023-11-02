/* eval.c - Weak language IR interpreter.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/eval.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ir.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include "util/vector.h"
#include <assert.h>
#include <string.h>



static void reset_hashmap(hashmap_t *map)
{
    if (map->buckets) {
        hashmap_destroy(map);
    }
    hashmap_init(map, 512);
}



/// key:   symbol index
/// value: immediate
static vector_t(hashmap_t *) storages;
static hashmap_t *storage_act;

static void storage_new()
{
    hashmap_t *map = weak_calloc(1, sizeof (hashmap_t));
    hashmap_init(map, 128);
    vector_push_back(storages, map);
    __weak_debug_msg("Allocated storage, count: %ld\n", storages.count);
}

void storage_pop()
{
    vector_foreach_back(storages, i) {
        hashmap_t *storage = vector_at(storages, i);
        if (storage == storage_act) {
            vector_erase(storages, i);
        }
    }
    __weak_debug_msg("Removed storage, count: %ld\n", storages.count);
}



hashmap_t *storage_callee()
{
    assert(storages.count > 0 && "Cannot get anything from empty storage.");
    return vector_at(storages, storages.count - 1);
}

hashmap_t *storage_caller()
{
    assert(storages.count > 1 && "Cannot get anything from empty storage.");
    return vector_at(storages, storages.count - 2);
}

static void storage_set_callee_active()
{
    __weak_debug_msg("Set callee storage active\n");
    storage_act = storage_callee();

    __weak_debug({
        hashmap_foreach(storage_act, k, v) {
            struct ir_imm imm = {0};
            memcpy(&imm, &v, sizeof (uint64_t));
            __weak_debug_msg("  \\ Callee storage: sym %%%ld: $%d\n", k, imm.imm.__int);
        }
    });
}

static void storage_set_caller_active()
{
    __weak_debug_msg("Set caller storage active\n");
    storage_act = storage_caller();

    __weak_debug({
        hashmap_foreach(storage_act, k, v) {
            struct ir_imm imm = {0};
            memcpy(&imm, &v, sizeof (uint64_t));
            __weak_debug_msg("  \\ Caller storage: sym %%%ld: $%d\n", k, imm.imm.__int);
        }
    });
}



static struct ir_imm storage_get(int32_t sym_idx)
{
    bool ok = 0;
    /// Whole `struct ir_imm` encoded in 64 bits.
    uint64_t got = hashmap_get(storage_act, sym_idx, &ok);
    if (!ok)
        weak_unreachable("Cannot get symbol %%%d from storage", sym_idx);

    struct ir_imm imm = {0};
    memcpy(&imm, &got, sizeof (uint64_t));
    return imm;
}



static void storage_set(int32_t sym_idx, struct ir_imm imm)
{
    uint64_t val = 0;
    memcpy(&val, &imm, sizeof (uint64_t));
    hashmap_put(storage_act, sym_idx, val);
    __weak_debug_msg("Put to storage idx: %%%d, value: %d\n", sym_idx, imm.imm.__int);
}



static struct ir_node *instr_pointer;
static hashmap_t jmp_table;

static void jmp_table_init(struct ir_node *ir)
{
    reset_hashmap(&jmp_table);

    struct ir_node *it = ir;
    while (it) {
        hashmap_put(&jmp_table, it->instr_idx, (uint64_t) it);
        it = it->next;
    }
}

static struct ir_node *jmp_table_get(int32_t instr_idx)
{
    bool ok = 0;
    uint64_t got = hashmap_get(&jmp_table, instr_idx, &ok);
    if (!ok)
        weak_unreachable("Jump table lookup failed: no instruction at index %d", instr_idx);

    return (struct ir_node *) got;
}



static struct ir_imm last_imm;

static void eval_func_call(struct ir_func_call *fcall);
static void eval_instr(struct ir_node *ir);

static void eval_imm(struct ir_imm *imm)
{
    last_imm = *imm;
}

static void eval_sym(struct ir_sym *sym)
{
    last_imm = storage_get(sym->idx);
}



static struct ir_imm eval_imm_imm_bool(enum token_type op, bool l, bool r)
{
    struct ir_imm imm = {
        .type = IMM_BOOL,
        .imm  = (union ir_imm_val) 0
    };

    switch (op) {
    case TOK_BIT_AND: imm.imm.__bool = l & r; break;
    case TOK_BIT_OR:  imm.imm.__bool = l | r; break;
    case TOK_XOR:     imm.imm.__bool = l ^ r; break;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }

    return imm;
}

static struct ir_imm eval_imm_imm_float(enum token_type op, float l, float r)
{
    struct ir_imm imm = {
        .type = IMM_FLOAT,
        .imm  = (union ir_imm_val) 0
    };

    switch (op) {
    case TOK_EQ:      imm.imm.__float = l == r; break;
    case TOK_NEQ:     imm.imm.__float = l != r; break;
    case TOK_GT:      imm.imm.__float = l  > r; break;
    case TOK_LT:      imm.imm.__float = l  < r; break;
    case TOK_GE:      imm.imm.__float = l >= r; break;
    case TOK_LE:      imm.imm.__float = l <= r; break;
    case TOK_PLUS:    imm.imm.__float = l  + r; break;
    case TOK_MINUS:   imm.imm.__float = l  - r; break;
    case TOK_STAR:    imm.imm.__float = l  * r; break;
    case TOK_SLASH:   imm.imm.__float = l  / r; break;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }

    return imm;
}

/// Integer and char supports same binary operations.
static struct ir_imm eval_imm_imm_integral(
    enum token_type  op,
    int32_t          l,
    int32_t          r,
    enum ir_imm_type t
) {
    struct ir_imm imm = {
        .type = t,
        .imm  = (union ir_imm_val) 0
    };

    switch (op) {
    case TOK_AND:     imm.imm.__int = l && r; break;
    case TOK_OR:      imm.imm.__int = l || r; break;
    case TOK_XOR:     imm.imm.__int = l  ^ r; break;
    case TOK_BIT_AND: imm.imm.__int = l  & r; break;
    case TOK_BIT_OR:  imm.imm.__int = l  | r; break;
    case TOK_EQ:      imm.imm.__int = l == r; break;
    case TOK_NEQ:     imm.imm.__int = l != r; break;
    case TOK_GT:      imm.imm.__int = l  > r; break;
    case TOK_LT:      imm.imm.__int = l  < r; break;
    case TOK_GE:      imm.imm.__int = l >= r; break;
    case TOK_LE:      imm.imm.__int = l <= r; break;
    case TOK_SHL:     imm.imm.__int = l << r; break;
    case TOK_SHR:     imm.imm.__int = l >> r; break;
    case TOK_PLUS:    imm.imm.__int = l  + r; break;
    case TOK_MINUS:   imm.imm.__int = l  - r; break;
    case TOK_STAR:    imm.imm.__int = l  * r; break;
    case TOK_SLASH:   imm.imm.__int = l  / r; break;
    case TOK_MOD:     imm.imm.__int = l  % r; break;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }

    return imm;
}

static struct ir_imm eval_imm_imm(
    enum   token_type op,
    struct ir_imm     l,
    struct ir_imm     r
) {
    switch (l.type) {
    case IMM_BOOL:  return eval_imm_imm_bool    (op, l.imm.__bool,  r.imm.__bool);
    case IMM_CHAR:  return eval_imm_imm_integral(op, l.imm.__char,  r.imm.__char, IMM_CHAR);
    case IMM_FLOAT: return eval_imm_imm_float   (op, l.imm.__float, r.imm.__float);
    case IMM_INT:   return eval_imm_imm_integral(op, l.imm.__int,   r.imm.__int, IMM_INT);
    default:
        weak_unreachable("Unknown immediate type (numeric: %d).", l.type);
    }
}

static void eval_bin(struct ir_bin *bin)
{
    eval_instr(bin->lhs);
    struct ir_imm l = last_imm;

    eval_instr(bin->rhs);
    struct ir_imm r = last_imm;

    last_imm = eval_imm_imm(bin->op, l, r);
}



static void eval_store_bin(struct ir_store *ir)
{
    eval_instr(ir->body);
    assert(ir->idx->type == IR_SYM && "TODO: Implement arrays");
    struct ir_sym *to_sym = ir->idx->ir;
    storage_set(to_sym->idx, last_imm);
}

static void eval_store_imm(struct ir_store *ir)
{
    assert(ir->idx->type == IR_SYM && "TODO: Implement arrays");
    struct ir_sym *to_sym = ir->idx->ir;
    struct ir_imm *imm = ir->body->ir;
    storage_set(to_sym->idx, *imm);
}

static void eval_store_sym(struct ir_store *ir)
{
    assert(ir->idx->type == IR_SYM && "TODO: Implement arrays");
    struct ir_sym *to_sym = ir->idx->ir;
    struct ir_sym *from_sym = ir->body->ir;
    struct ir_imm imm = storage_get(from_sym->idx);
    storage_set(to_sym->idx, imm);
}

static void eval_store_call(struct ir_store *ir)
{
    struct ir_func_call *fcall = ir->body->ir;
    assert(ir->idx->type == IR_SYM && "TODO: Implement arrays");
    struct ir_sym *to_sym = ir->idx->ir;
    eval_func_call(fcall);
    storage_set(to_sym->idx, last_imm);
}

static void eval_store(struct ir_store *store)
{
    switch (store->body->type) {
    case IR_IMM: {
        eval_store_imm(store);
        break;
    }
    case IR_SYM: {
        eval_store_sym(store);
        break;
    }
    case IR_BIN: {
        // Some error there.
        eval_store_bin(store);
        break;
    }
    case IR_FUNC_CALL: {
        eval_store_call(store);
        break;
    }
    default:
        break;
    }
}

static void eval_cond(struct ir_cond *cond)
{
    eval_instr(cond->cond);

    bool should_jump;
    switch (last_imm.type) {
    case IMM_BOOL:  should_jump = last_imm.imm.__bool; break;
    case IMM_CHAR:  should_jump = last_imm.imm.__char != '\0'; break;
    case IMM_FLOAT: should_jump = last_imm.imm.__float != 0.0; break;
    case IMM_INT:   should_jump = last_imm.imm.__int != 0; break;
    default:
        weak_unreachable("Unknown immediate type (numeric: %d).", last_imm.type);
    }

    if (should_jump)
        instr_pointer = vector_at(jmp_table_get(cond->goto_label)->prev, 0);
}

static void eval_jmp(struct ir_jump *jmp)
{
    /// Prev is due eval_fun() execution loop specific algorithm.
    instr_pointer = vector_at(jmp_table_get(jmp->idx)->prev, 0);
}

static void eval_ret(struct ir_ret *ret)
{
    if (ret->is_void)
        return;

    eval_instr(ret->body);

    instr_pointer = NULL;
}



static void eval_instr(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        break;
    case IR_IMM:
        eval_imm(ir->ir);
        break;
    case IR_SYM:
        eval_sym(ir->ir);
        break;
    case IR_JUMP:
        eval_jmp(ir->ir);
        break;
    case IR_MEMBER:
    case IR_TYPE_DECL:
        break;
    case IR_FUNC_DECL:
        break;
    case IR_FUNC_CALL:
        eval_func_call(ir->ir);
        break;
    case IR_STORE:
        eval_store(ir->ir);
        break;
    case IR_BIN:
        eval_bin(ir->ir);
        break;
    case IR_RET:
    case IR_RET_VOID:
        eval_ret(ir->ir);
        break;
    case IR_COND:
        eval_cond(ir->ir);
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
    jmp_table_init(it);

    instr_pointer = it;

    while (instr_pointer) {
        eval_instr(instr_pointer);

        /// If instruction pointer was set to NULL,
        /// then `ret` instruction was interpreted,
        /// code should exit now.
        if (instr_pointer)
            instr_pointer = instr_pointer->next;
    }
}

/// Preconditions:
/// 1) Allocated storage
/// 2) Computed and pushed to it arguments
static void call(const char *name)
{
    __weak_debug_msg("Calling `%s`\n", name);

    struct ir_node *saved = instr_pointer;

    struct ir_func_decl *func = function_list_lookup(name);
    eval_func_decl(func);

    instr_pointer = saved;

    __weak_debug_msg("Exiting `%s`\n", name);
}

static void eval_func_call(struct ir_func_call *fcall)
{
    storage_new();

    int32_t sym_idx = 0;

    struct ir_node *it = fcall->args;
    while (it) {
        /// Copy from caller to callee.
        storage_set_caller_active();
        eval_instr(it);
        storage_set_callee_active();
        storage_set(sym_idx++, last_imm);
        it = it->next;
    }

    call(fcall->name);

    storage_pop();
    storage_set_callee_active();
}



static void reset_all()
{
    vector_foreach(storages, i) {
        hashmap_t *storage = vector_at(storages, i);
        hashmap_destroy(storage);
    }
    vector_free(storages);

    reset_hashmap(&function_list);
    reset_hashmap(&jmp_table);
    instr_pointer = NULL;
}

int32_t eval(struct ir_node *ir)
{
    reset_all();

    struct ir_node *it = ir;

    while (it) {
        struct ir_func_decl *func = it->ir;
        hashmap_put(&function_list, crc32_string(func->name), (uint64_t) func);
        it = it->next;
    }

    __weak_debug({
        hashmap_foreach(&function_list, k, v) {
            (void) k;
            struct ir_func_decl *func = (struct ir_func_decl *) v;
            __weak_debug_msg("Function in list: `%s`\n", func->name);
        }
    });

    /// Allocate storage there manually. Allocated also
    /// in eval_func_call().
    storage_new();
    storage_set_callee_active();
    call("main");
    storage_pop();

    return last_imm.imm.__int;
}