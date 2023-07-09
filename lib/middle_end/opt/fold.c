/* fold.c - Constant folding.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/ir/dump.h"
#include "middle_end/opt/opt.h"
#include "util/compiler.h"
#include "util/hashmap.h"
#include "util/vector.h"
#include "util/unreachable.h"
#include <string.h>
#include <assert.h>

/// Hashmap to refer by variable index.
static hashmap_t alloca_stmts;
static hashmap_t consts_mapping;

static vector_t(uint64_t) redundant_stmts;

static void consts_mapping_init()
{
    if (consts_mapping.buckets) {
        hashmap_destroy(&consts_mapping);
    }
    hashmap_init(&consts_mapping, 512);

    if (alloca_stmts.buckets) {
        hashmap_destroy(&alloca_stmts);
    }
    hashmap_init(&alloca_stmts, 512);

    vector_clear(redundant_stmts);
}

static void consts_mapping_add(uint64_t idx, uint64_t value)
{
    hashmap_put(&consts_mapping, idx, value);
}

static void consts_mapping_remove(uint64_t idx)
{
    hashmap_remove(&consts_mapping, idx);
}

static union ir_imm_val consts_mapping_get(uint64_t idx)
{
    uint64_t got = hashmap_get(&consts_mapping, idx);
    return (union ir_imm_val) (int32_t) got;
}

static void consts_mapping_update(uint64_t idx, uint64_t value)
{
    hashmap_remove(&consts_mapping, idx);
    hashmap_put(&consts_mapping, idx, value);
}

static bool consts_mapping_is_const(uint64_t idx)
{
    return hashmap_get(&consts_mapping, idx) != 0;
}

static void alloca_stmts_put(uint64_t sym_idx, uint64_t instr_idx)
{
    /// Note: this hashmap does not allow to have key 0, so there
    ///       is hack with INT64_MAX.
    uint64_t key =
        sym_idx == 0
            ? INT64_MAX
            : sym_idx;

    uint64_t val =
        instr_idx == 0
            ? INT64_MAX
            : instr_idx;

    hashmap_put(&alloca_stmts, key, val);
}

static void alloca_stmts_remove(uint64_t sym_idx)
{
    hashmap_remove(&alloca_stmts, sym_idx);
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

__weak_wur __weak_unused static struct ir_node compute_imm(
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

static struct ir_node fold_node(struct ir_node *ir);

static struct ir_node no_result()
{
    struct ir_node node = {
        .instr_idx = -1,
        .ir        = NULL,
        .idom      = NULL
    };

    return node;
}

__weak_unused static bool is_no_result(struct ir_node *ir)
{
    return
        ir->instr_idx ==   -1 &&
        ir->ir        == NULL &&
        ir->idom      == NULL;
}

static struct ir_node fold_sym(struct ir_sym *ir)
{
    if (consts_mapping_is_const(ir->idx)) {
        return ir_imm_int_init(consts_mapping_get(ir->idx).__int);
    }

    return no_result();
}

static struct ir_node fold_imm(struct ir_imm *ir)
{
    return ir_imm_int_init(ir->imm.__int);
}

static void fold_store_bin(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    struct ir_node folded = fold_node(&store->body);

    if (is_no_result(&folded)) {
        consts_mapping_remove(store->idx);
        alloca_stmts_remove(store->idx);
    }

    /// The value returned from store argument fold is
    /// binary or immediate values. No symbols returned.
    if (folded.type == IR_BIN) {
        ir_node_cleanup(store->body);
        store->body = folded;
        store->type = IR_STORE_BIN;
        consts_mapping_remove(store->idx);
        alloca_stmts_remove(store->idx);
    }

    if (folded.type == IR_IMM) {
        struct ir_imm *imm = folded.ir;

        ir_node_cleanup(store->body);
        store->body = folded;
        store->type = IR_STORE_IMM;
        consts_mapping_update(store->idx, imm->imm.__int);
        vector_push_back(redundant_stmts, ir->instr_idx);
    }
}

static void fold_store_sym(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    struct ir_sym *sym = store->body.ir;

    if (consts_mapping_is_const(sym->idx)) {
        union ir_imm_val imm = consts_mapping_get(sym->idx);

        ir_node_cleanup(store->body);
        /// \todo: Any type
        store->body = ir_imm_int_init(imm.__int);
        store->type = IR_STORE_IMM;

        consts_mapping_update(store->idx, imm.__int);
        vector_push_back(redundant_stmts, ir->instr_idx);
    } else {
        consts_mapping_remove(store->idx);
        alloca_stmts_remove(store->idx);
    }
}

static void fold_store_imm(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    struct ir_imm *imm = store->body.ir;

    if (consts_mapping_is_const(store->idx)) {
        consts_mapping_update(store->idx, imm->imm.__int);
    } else {
        consts_mapping_add(store->idx, imm->imm.__int);
    }

    vector_push_back(redundant_stmts, ir->instr_idx);
}

static void fold_store(struct ir_node *ir)
{
    struct ir_store *store = ir->ir;
    switch (store->type) {
    case IR_STORE_BIN: {
        fold_store_bin(ir);
        break;
    }
    case IR_STORE_SYM: {
        fold_store_sym(ir);
        break;
    }
    case IR_STORE_IMM: {
        fold_store_imm(ir);
        break;
    }
    default:
        break;
    }
}

static struct ir_node fold_bin(struct ir_bin *ir)
{
    struct ir_node l = fold_node(&ir->lhs);
    struct ir_node r = fold_node(&ir->rhs);

    if (l.type == IR_IMM && r.type == IR_IMM) {
        struct ir_imm *l_imm = l.ir;
        struct ir_imm *r_imm = r.ir;

        return compute_imm(ir->op, l_imm->type, l_imm->imm, r_imm->imm);
    }

    return ir_bin_init(
        ir->op,
        is_no_result(&l) ? ir_sym_init( ((struct ir_sym *) ir->lhs.ir)->idx) : l,
        is_no_result(&r) ? ir_sym_init( ((struct ir_sym *) ir->rhs.ir)->idx) : r
    );
}

static void fold_ret(struct ir_ret *ir)
{
    if (ir->is_void) return;

    struct ir_sym *sym = ir->op.ir;

    if (consts_mapping_is_const(sym->idx)) {
        union ir_imm_val imm = consts_mapping_get(sym->idx);

        /// \todo: Immediate emit for all types.
        ir_node_cleanup(ir->op);
        ir->op = ir_imm_int_init(imm.__int);
    }
}

static void fold_cond(struct ir_cond *ir)
{
    fold_node(&ir->cond);
}

static void fold_alloca(struct ir_node *ir)
{
    struct ir_alloca *alloca = ir->ir;

    alloca_stmts_put(alloca->idx, ir->instr_idx);
}

static struct ir_node fold_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        fold_alloca(ir);
        break;
    case IR_IMM:
        return fold_imm(ir->ir);
    case IR_SYM:
        return fold_sym(ir->ir);
    case IR_LABEL:
    case IR_JUMP:
    case IR_MEMBER:
    case IR_ARRAY_ACCESS:
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

/// \todo: Complexity optimization.
static void fold_remove_redundant_stmts(struct ir_func_decl *decl)
{
    /// Vector is used for convenient erasure.
    vector_t(struct ir_node) stmts;

    stmts.data  = decl->body;
    stmts.count = decl->body_size;
    stmts.size  = stmts.count * sizeof (struct ir_node *);

    vector_foreach_back(redundant_stmts, i) {
        uint64_t idx = vector_at(redundant_stmts, i);
        vector_foreach_back(stmts, j) {
            if (vector_at(stmts, j).instr_idx == (int32_t) idx) {
                vector_erase(stmts, j);
            }
        }
    }

    hashmap_foreach(&alloca_stmts, k, v) {
        (void) k;
        /// Note: this hashmap does not allow to have key 0, so there
        ///       is hack with INT64_MAX.
        uint64_t instr_idx = v == INT64_MAX ? 0 : v;
        vector_foreach_back(stmts, i) {
            if (vector_at(stmts, i).instr_idx == (int32_t) instr_idx) {
                vector_erase(stmts, i);
            }
        }
    }

    decl->body_size = stmts.count;
}

static void fold(struct ir_func_decl *decl)
{
    for (uint64_t i = 0; i < decl->body_size; ++i) {
        struct ir_node *node = &decl->body[i];
        fold_node(node);
    }

    fold_remove_redundant_stmts(decl);
}

void ir_opt_fold(struct ir *ir)
{
    consts_mapping_init();

    for (uint64_t i = 0; i < ir->decls_size; ++i) {
        struct ir_func_decl *decl = ir->decls[i].ir;
        fold(decl);
    }
}