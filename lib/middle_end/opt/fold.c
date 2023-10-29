/* fold.c - Constant folding.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/ir/meta.h"
#include "middle_end/opt/opt.h"
#include "util/compiler.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include <string.h>

/* Hashmap to refer by variable index. */
static hashmap_t consts_mapping;
static hashmap_t loop_dependent_stmts;

static void reset_hashmap(hashmap_t *map)
{
    if (map->buckets) {
        hashmap_destroy(map);
    }
    hashmap_init(map, 512);
}

static void fold_opt_reset()
{
    reset_hashmap(&consts_mapping);
    reset_hashmap(&loop_dependent_stmts);
}

static void consts_mapping_add(uint64_t idx, uint64_t value)
{
    __weak_debug_msg("Consts mapping: put %ld:%ld\n", idx, value);
    hashmap_put(&consts_mapping, idx, value);
}

static void consts_mapping_remove(uint64_t idx)
{
    __weak_debug_msg("Consts mapping: remove %ld\n", idx);
    hashmap_remove(&consts_mapping, idx);
}

static union ir_imm_val consts_mapping_get(uint64_t idx)
{
    bool ok = 0;
    int64_t got = hashmap_get(&consts_mapping, idx, &ok);
    if (!ok) {
        weak_unreachable("Cannot get by index %ld", idx);
    }
    __weak_debug_msg("Consts mapping: get %ld:%ld\n", idx, got);
    return (union ir_imm_val) (int32_t) got;
}

static void consts_mapping_update(uint64_t idx, uint64_t value)
{
    hashmap_remove(&consts_mapping, idx);
    __weak_debug_msg("Consts mapping: update %ld:%ld\n", idx, value);
    hashmap_put(&consts_mapping, idx, value);
}

static bool consts_mapping_is_const(uint64_t idx)
{
    bool ok = 0;
    hashmap_get(&consts_mapping, idx, &ok);
    __weak_debug_msg("Consts mapping: is const? idx:%ld -> %d\n", idx, ok);
    return ok;
}

static void loop_dependent_put(uint64_t sym_idx, uint64_t loop_idx)
{
    __weak_debug_msg("Loop dependence mapping: add idx:%ld, loop_idx:%ld\n", sym_idx, loop_idx);
    hashmap_put(&loop_dependent_stmts, sym_idx, loop_idx);
}

static bool loop_dependent(uint64_t sym_idx)
{
    bool ok = 0;
    hashmap_get(&loop_dependent_stmts, sym_idx, &ok);
    __weak_debug_msg("Loop dependence mapping: is depends on loop conditions? idx:%ld -> %d\n", sym_idx, ok);
    return ok;
}

static bool fold_booleans(enum token_type op, bool l, bool r)
{
    switch (op) {
    case TOK_BIT_AND: return l & r;
    case TOK_BIT_OR:  return l | r;
    case TOK_XOR:     return l ^ r;
    case TOK_ASSIGN:  return 0;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }
}

static int32_t fold_ints(enum token_type op, int32_t l, int32_t r)
{
    switch (op) {
    case TOK_AND:     return l && r;
    case TOK_OR:      return l || r;
    case TOK_XOR:     return l  ^ r;
    case TOK_BIT_AND: return l  & r;
    case TOK_BIT_OR:  return l  | r;
    case TOK_EQ:      return l == r;
    case TOK_NEQ:     return l != r;
    case TOK_GT:      return l  > r;
    case TOK_LT:      return l  < r;
    case TOK_GE:      return l >= r;
    case TOK_LE:      return l <= r;
    case TOK_SHL:     return l << r;
    case TOK_SHR:     return l >> r;
    case TOK_PLUS:    return l  + r;
    case TOK_MINUS:   return l  - r;
    case TOK_STAR:    return l  * r;
    case TOK_SLASH:   return l  / r;
    case TOK_MOD:     return l  % r;
    case TOK_ASSIGN:  return -1;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }
}

static float fold_floats(enum token_type op, float l, float r)
{
    switch (op) {
    case TOK_EQ:      return l == r;
    case TOK_NEQ:     return l != r;
    case TOK_GT:      return l  > r;
    case TOK_LT:      return l  < r;
    case TOK_GE:      return l >= r;
    case TOK_LE:      return l <= r;
    case TOK_PLUS:    return l  + r;
    case TOK_MINUS:   return l  - r;
    case TOK_STAR:    return l  * r;
    case TOK_SLASH:   return l  / r;
    case TOK_ASSIGN:  return -1.0;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }
}

__weak_wur static struct ir_node *compute_imm(
    enum  token_type  op,
    enum  ir_imm_type type,
    union ir_imm_val  lhs,
    union ir_imm_val  rhs
) {
    switch (type) {
    case IMM_BOOL:  return ir_imm_bool_init (fold_booleans(op, lhs.__bool,  rhs.__bool));
    case IMM_CHAR:  return ir_imm_char_init (fold_ints    (op, lhs.__char,  rhs.__char));
    case IMM_FLOAT: return ir_imm_float_init(fold_floats  (op, lhs.__float, rhs.__float));
    case IMM_INT:   return ir_imm_int_init  (fold_ints    (op, lhs.__int,   rhs.__int));
    default:
        weak_unreachable("Unknown immediate IR type (numeric: %d).", type);
    }
}

static struct ir_node *fold_node(struct ir_node *ir);

__weak_wur static struct ir_node *no_result()
{
    static struct ir_node ir = {0};
    ir.instr_idx = -1;
    ir.ir = NULL;
    ir.idom = NULL;
    return &ir;
}

__weak_wur static bool is_no_result(struct ir_node *ir)
{
    if (!ir) return 1;
    return ir == no_result();
}

static uint64_t get_store_idx(struct ir_node *ir)
{
    struct ir_sym *store = ir->ir;
    return store->idx;
}

static struct ir_node *fold_sym(struct ir_sym *ir)
{
    if (consts_mapping_is_const(ir->idx))
        return ir_imm_int_init(consts_mapping_get(ir->idx).__int);

    return no_result();
}

static struct ir_node *fold_imm(struct ir_imm *ir)
{
    return ir_imm_int_init(ir->imm.__int);
}

static bool fold_store_mark_loop_dependent(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;

    if (ir->meta.sym_meta.loop) {
        loop_dependent_put(get_store_idx(store->idx), ir->meta.sym_meta.loop_idx);
        __weak_debug_msg("Added loop-dependent variable (loop attr) %%%d. Return\n", store->idx);
        return 1;
    }
    return 0;
}

static void fold_store_bin(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;

    if (ir->meta.type != IR_META_UNKNOWN)
        if (fold_store_mark_loop_dependent(ir))
            return;

    if (loop_dependent(get_store_idx(store->idx)))
        return;

    struct ir_node *folded = fold_node(store->body);

    if (is_no_result(folded))
        return;

    switch (folded->type) {
    case IR_BIN: {
        ir_node_cleanup(store->body);
        store->body = folded;
        break;
    }
    case IR_IMM: {
        struct ir_imm *imm = folded->ir;
        ir_node_cleanup(store->body);
        store->body = folded;
        consts_mapping_update(get_store_idx(store->idx), imm->imm.__int);
        break;
    }
    default:
        break;
    }
}

static void fold_store_sym(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    struct ir_sym *sym = store->body->ir;

    if (ir->meta.type != IR_META_UNKNOWN)
        if (fold_store_mark_loop_dependent(ir))
            return;

    if (consts_mapping_is_const(sym->idx)) {
        union ir_imm_val imm = consts_mapping_get(sym->idx);

        ir_node_cleanup(store->body);
        /// \todo: Any type
        store->body = ir_imm_int_init(imm.__int);
        // store->type = IR_STORE_IMM;

        consts_mapping_update(get_store_idx(store->idx), imm.__int);
    } else {
        consts_mapping_remove(get_store_idx(store->idx));
    }
}

static void fold_store_imm(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    struct ir_imm   *imm = store->body->ir;

    if (ir->meta.type != IR_META_UNKNOWN)
        if (fold_store_mark_loop_dependent(ir))
            return;

    if (consts_mapping_is_const(get_store_idx(store->idx))) {
        consts_mapping_update(get_store_idx(store->idx), imm->imm.__int);
    } else {
        consts_mapping_add(get_store_idx(store->idx), imm->imm.__int);
    }
}

static void fold_store(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    switch (store->body->type) {
    case IR_BIN: {
        fold_store_bin(ir);
        break;
    }
    case IR_SYM: {
        fold_store_sym(ir);
        break;
    }
    case IR_IMM: {
        fold_store_imm(ir);
        break;
    }
    default:
        break;
    }
}

/* This function tries to reduce binary statement
   with respect to @noalias attribute. Symbols marked
   with @noalias are always left as is. */
static struct ir_node *fold_bin(struct ir_bin *ir)
{
    struct ir_node *l = NULL;
    struct ir_node *r = NULL;

    if (ir->lhs->meta.type != IR_META_UNKNOWN) {
        struct meta *meta = &ir->lhs->meta;
        if (!meta->sym_meta.noalias) {
            l = fold_node(ir->lhs);
        } else {
            __weak_debug_msg("Found noalias attribute for %%%d\n", ir->lhs->instr_idx);
        }
    } else {
        l = fold_node(ir->lhs);
    }

    if (l) {
        __weak_debug_msg("Bin: folded LHS -> ");
        __weak_debug({
            if (!is_no_result(l)) {
                ir_dump_node(stdout, l);
            } else {
                printf(" <NO RESULT>");
            }
            puts("");
        });
    }

    if (ir->rhs->meta.type != IR_META_UNKNOWN) {
        struct meta *meta = &ir->rhs->meta;
        if (!meta->sym_meta.noalias) {
            r = fold_node(ir->rhs);
        } else {
            __weak_debug_msg("Found noalias attribute for %%%d\n", ir->rhs->instr_idx);
        }
    } else {
        r = fold_node(ir->rhs);
    }

    if (r) {
        __weak_debug_msg("Bin: folded RHS -> ");
        __weak_debug({
            if (!is_no_result(r)) {
                ir_dump_node(stdout, r);
            } else {
                printf(" <NO RESULT>");
            }
            puts("");
        });
    }

    if (l && r && l->type == IR_IMM && r->type == IR_IMM) {
        struct ir_imm *l_imm = l->ir;
        struct ir_imm *r_imm = r->ir;

        return compute_imm(ir->op, l_imm->type, l_imm->imm, r_imm->imm);
    }

    if (l && l->type == IR_SYM) {
        struct ir_sym *sym = l->ir;

        if (loop_dependent(sym->idx))
            return no_result();
    }

    if (r && r->type == IR_SYM) {
        struct ir_sym *sym = r->ir;

        if (loop_dependent(sym->idx))
            return no_result();
    }

    /* Attributes are lost, but this is not much important. */
    return ir_bin_init(
        ir->op,
        is_no_result(l) ? ir_sym_init( ((struct ir_sym *) ir->lhs->ir)->idx) : l,
        is_no_result(r) ? ir_sym_init( ((struct ir_sym *) ir->rhs->ir)->idx) : r
    );
}

static void fold_ret(struct ir_ret *ir)
{
    if (ir->is_void) return;

    struct ir_sym *sym = ir->body->ir;

    if (consts_mapping_is_const(sym->idx)) {
        union ir_imm_val imm = consts_mapping_get(sym->idx);

        /* TODO: Immediate emit for all types. */
        ir_node_cleanup(ir->body);
        ir->body = ir_imm_int_init(imm.__int);
    }
}

static void fold_cond(struct ir_cond *ir)
{
    fold_node(ir->cond);
}

static struct ir_node *fold_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        break;
    case IR_IMM:
        return fold_imm(ir->ir);
    case IR_SYM:
        return fold_sym(ir->ir);
    case IR_JUMP:
    case IR_MEMBER:
    case IR_TYPE_DECL:
    case IR_FUNC_DECL:
    case IR_FUNC_CALL:
        break;
    case IR_STORE:
        fold_store(ir);
        break;
    case IR_BIN:
        return fold_bin(ir->ir);
    case IR_RET:
    case IR_RET_VOID:
        fold_ret(ir->ir);
        break;
    case IR_COND:
        fold_cond(ir->ir);
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }

    return no_result();
}

void ir_opt_fold(struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;
    uint64_t cfg_no = 0;

    while (it) {
        bool should_reset = 0;
        should_reset |= it == decl->body;
        should_reset |= cfg_no != it->cfg_block_no;

        fold_node(it);
        if (should_reset)
            fold_opt_reset();

        cfg_no = it->cfg_block_no;
        it = it->next;
    }
}