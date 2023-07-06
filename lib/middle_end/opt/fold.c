/* fold.c - Constant folding.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/opt/opt.h"
#include "util/compiler.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include <string.h>
#include <assert.h>

/// \todo: *) Constants mapping for all types.
///        *) Remove dead store and alloca.
///        *) Refactor. This code was written in 30 minutes.
///           Requiers some meditation process.
static struct ir_node last_folded;
static hashmap_t      consts_mapping;

static void consts_mapping_init()
{
    if (consts_mapping.buckets) {
        hashmap_destroy(&consts_mapping);
    }
    hashmap_init(&consts_mapping, 512);
}

__weak_really_inline static void consts_mapping_add(uint64_t idx, uint64_t value)
{
    hashmap_put(&consts_mapping, idx, value);
    printf("Consts mapping: add idx:%ld, value:%ld\n", idx, value);
}

__weak_really_inline static uint64_t consts_mapping_get(uint64_t idx)
{
    uint64_t got = hashmap_get(&consts_mapping, idx);
    printf("Consts mapping: get value of idx:%ld -> %ld\n", idx, got);
    return got;
}

__weak_really_inline static void consts_mapping_update(uint64_t idx, uint64_t value)
{   
    hashmap_remove(&consts_mapping, idx);
    hashmap_put(&consts_mapping, idx, value);
    printf("Consts mapping: update idx:%ld, value:%ld\n", idx, value);
}

__weak_really_inline static bool consts_mapping_is_const(uint64_t idx)
{
    uint64_t got = hashmap_get(&consts_mapping, idx);
    printf("Consts mapping: is_const? idx:%ld -> %s\n", idx, (got != 0) ? "yes" : "no");
    return got != 0;
}

__weak_really_inline static bool fold_booleans(enum token_type op, bool l, bool r)
{
    switch (op) {
    case TOK_BIT_AND: return l & r;
    case TOK_BIT_OR:  return l | r;
    case TOK_XOR:     return l ^ r;
    default:
        weak_unreachable("Something went wrong.");
    }
}

__weak_really_inline static int32_t fold_ints(enum token_type op, int32_t l, int32_t r)
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
    default:
        weak_unreachable("Something went wrong.");
    }
}

__weak_really_inline static float fold_floats(enum token_type op, float l, float r)
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
    default:
        weak_unreachable("Something went wrong.");
    }
}

static void fold_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA: {
        struct ir_alloca *l = ir->ir;
        (void) l;
        break;
    }
    case IR_IMM: {
        struct ir_imm *l = ir->ir;
        switch (l->type) {
        case IMM_BOOL:
            break;
        case IMM_CHAR:
            break;
        case IMM_FLOAT:
            break;
        case IMM_INT:
            break;
        default:
            break;
        }
        break;
    }
    case IR_SYM: {
        struct ir_sym *l = ir->ir;
        (void) l;
        break;
    }
    case IR_LABEL: {
        struct ir_label *l = ir->ir;
        (void) l;
        break;
    }
    case IR_JUMP: {
        struct ir_jump *l = ir->ir;
        (void) l;
        break;
    }
    case IR_STORE: {
        struct ir_store *stmt = ir->ir;
        switch (stmt->type) {
        case IR_STORE_BIN: {
            struct ir_bin *bin = stmt->body.ir;

            if (bin->lhs.type == IR_IMM &&
                bin->rhs.type == IR_IMM) {
                fold_node(&stmt->body);
                ir_node_cleanup(stmt->body);
                stmt->body = last_folded;
                stmt->type = IR_STORE_IMM;

                struct ir_imm *imm = stmt->body.ir;
                consts_mapping_add(stmt->idx, imm->imm_int);
            }

            if ((bin->lhs.type == IR_SYM &&
                 bin->rhs.type == IR_IMM
                ) || (
                 bin->lhs.type == IR_SYM &&
                 bin->rhs.type == IR_SYM
                )
            ) {
                struct ir_sym *sym = bin->lhs.ir;

                if (consts_mapping_is_const(sym->idx)) {
                    fold_node(&stmt->body);
                    ir_node_cleanup(stmt->body);
                    stmt->body = last_folded;
                    stmt->type = IR_STORE_IMM;

                    struct ir_imm *imm = stmt->body.ir;
                    consts_mapping_update(stmt->idx, imm->imm_int);
                }
            }

            break;
        }
        case IR_STORE_VAR: {
            struct ir_sym *sym = stmt->body.ir;

            if (consts_mapping_is_const(sym->idx)) {
                /// \todo: Get any type (ints, floats, etc);
                uint64_t imm = consts_mapping_get(sym->idx);

                ir_node_cleanup(stmt->body);
                stmt->body = ir_imm_int_init(imm);
                stmt->type = IR_STORE_IMM;

                consts_mapping_update(stmt->idx, imm);
            }
            break;
        }
        case IR_STORE_IMM: {
            struct ir_imm *imm = stmt->body.ir;

            if (consts_mapping_is_const(stmt->idx)) {
                consts_mapping_update(stmt->idx, imm->imm_int);
            }
        }
        default:
            break;
        }
        break;
    }
    case IR_BIN: {
        struct ir_bin *l = ir->ir;
        if (l->lhs.type == IR_IMM &&
            l->rhs.type == IR_IMM) {
            printf("Both immediates\n");

            struct ir_imm *l_imm = l->lhs.ir;
            struct ir_imm *r_imm = l->rhs.ir;
            assert(l_imm->type == r_imm->type);
            switch (l_imm->type) {
            case IMM_BOOL:
                last_folded = ir_imm_bool_init(fold_booleans(l->op, l_imm->imm_bool, r_imm->imm_bool));
                break;
            case IMM_CHAR:
                last_folded = ir_imm_char_init(fold_ints(l->op, l_imm->imm_char, r_imm->imm_char));
                break;
            case IMM_FLOAT:
                last_folded = ir_imm_float_init(fold_floats(l->op, l_imm->imm_float, r_imm->imm_float));
                break;
            case IMM_INT:
                last_folded = ir_imm_int_init(fold_ints(l->op, l_imm->imm_int, r_imm->imm_int));
                break;
            }
        }

        if (l->lhs.type == IR_SYM &&
            l->rhs.type == IR_IMM) {
            printf("Symbol and immediate\n");

            struct ir_sym *sym = l->lhs.ir;
            struct ir_imm *imm = l->rhs.ir;

            if (consts_mapping_is_const(sym->idx)) {
                uint64_t imm_val = consts_mapping_get(sym->idx);

                switch (imm->type) {
                case IMM_BOOL:
                    last_folded = ir_imm_bool_init(fold_booleans(l->op, imm_val, imm->imm_bool));
                    break;
                case IMM_CHAR:
                    last_folded = ir_imm_char_init(fold_ints(l->op, imm_val, imm->imm_char));
                    break;
                case IMM_FLOAT:
                    last_folded = ir_imm_float_init(fold_floats(l->op, imm_val, imm->imm_float));
                    break;
                case IMM_INT:
                    last_folded = ir_imm_int_init(fold_ints(l->op, imm_val, imm->imm_int));
                    break;
                }
            }
        }

        if (l->lhs.type == IR_SYM &&
            l->rhs.type == IR_SYM) {
            struct ir_sym *sym_lhs = l->lhs.ir;
            struct ir_sym *sym_rhs = l->rhs.ir;

            printf("Both symbols\n");

            bool lhs_const = consts_mapping_is_const(sym_lhs->idx);
            bool rhs_const = consts_mapping_is_const(sym_rhs->idx);

            if (lhs_const && rhs_const) {
                uint64_t lhs_imm = consts_mapping_get(sym_lhs->idx);
                uint64_t rhs_imm = consts_mapping_get(sym_rhs->idx);

                /// Note: LHS and RHS types are the same.
                ///       IR generator post-condition.
                switch (IMM_INT) { /// Placeholder.
                case IMM_BOOL:
                    last_folded = ir_imm_bool_init(fold_booleans(l->op, lhs_imm, rhs_imm));
                    break;
                case IMM_CHAR:
                    last_folded = ir_imm_char_init(fold_ints(l->op, lhs_imm, rhs_imm));
                    break;
                case IMM_FLOAT:
                    last_folded = ir_imm_float_init(fold_floats(l->op, lhs_imm, rhs_imm));
                    break;
                case IMM_INT:
                    last_folded = ir_imm_int_init(fold_ints(l->op, lhs_imm, rhs_imm));
                    break;
                }
            }
        }
        break;
    }
    case IR_COND: {
        struct ir_cond *l = ir->ir;
        (void) l;
        break;
    }
    case IR_RET:
    case IR_RET_VOID: {
        struct ir_ret *stmt = ir->ir;
        if (!stmt->is_void) {
            struct ir_sym *sym = stmt->op.ir;

            if (consts_mapping_is_const(sym->idx)) {
                uint64_t imm = consts_mapping_get(sym->idx);

                /// \todo: Immediate emit for all types.
                ir_node_cleanup(stmt->op);
                stmt->op = ir_imm_int_init(imm);
            }
        }
        break;
    }
    case IR_MEMBER:
    case IR_ARRAY_ACCESS:
    case IR_TYPE_DECL:
    case IR_FUNC_DECL:
    case IR_FUNC_CALL: {
        break;
    }
    default:
        weak_unreachable("Something went wrong.");
    }
}

static void fold(struct ir_func_decl *decl)
{
    for (uint64_t i = 0; i < decl->body_size; ++i) {
        struct ir_node *node = &decl->body[i];
        fold_node(node);
   }
}

void ir_opt_fold(struct ir *ir)
{
    consts_mapping_init();

    for (uint64_t i = 0; i < ir->decls_size; ++i) {
        struct ir_func_decl *decl = ir->decls[i].ir;
        fold(decl);
    }
}