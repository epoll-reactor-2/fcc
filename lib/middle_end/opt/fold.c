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

static struct ir_node last_folded;
static hashmap_t      consts_mapping;

static void consts_mapping_init()
{
    if (consts_mapping.buckets) {
        hashmap_destroy(&consts_mapping);
    }
    hashmap_init(&consts_mapping, 512);
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
        struct ir_store *l = ir->ir;
        switch (l->type) {
        case IR_STORE_BIN: {
            fold_node(&l->body);
            ir_node_cleanup(l->body);
            l->body = last_folded;
            l->type = IR_STORE_IMM;
            break;
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
            struct ir_imm *l_imm = l->lhs.ir;
            struct ir_imm *r_imm = l->rhs.ir;
            assert(l_imm->type == r_imm->type);
            switch (l_imm->type) {
            case IMM_BOOL:
                last_folded = ir_imm_bool_init(fold_booleans(l->op, l_imm->imm_bool, r_imm->imm_bool));
                break;
            case IMM_CHAR:
                last_folded = ir_imm_char_init(fold_ints(l->op, l_imm->imm_bool, r_imm->imm_bool));
                break;
            case IMM_FLOAT:
                last_folded = ir_imm_float_init(fold_floats(l->op, l_imm->imm_bool, r_imm->imm_bool));
                break;
            case IMM_INT:
                last_folded = ir_imm_int_init(fold_ints(l->op, l_imm->imm_bool, r_imm->imm_bool));
                break;
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
        struct ir_ret *l = ir->ir;
        (void) l;
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
        /// \todo: Fold binary expressions chain to one
        ///        instructions.
        ///
        ///        1 + 2 + 3 ->
        ///
        ///        alloca int %0
        ///        store %0 2 + 3
        ///        alloca int %1
        ///        store %1 %0 + 1
        ///
        ///        ->
        ///
        ///        alloca int %0    ... Remove everything below
        ///        store %0 5
        ///
        ///        Properties:
        ///          if (is_const(%0)) ...
        ///
        ///        If there we store this way, maybe
        ///        the rest of the job will do
        ///        constant propagation algorithm?..
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