/* arith.c - Arithmetic optimizations.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/opt/opt.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ir.h"
#include "util/unreachable.h"
#include <assert.h>

static struct ir_node *opt_arith_node(struct ir_node *ir);

static struct ir_node *no_result()
{
    struct ir_node * ir = ir_node_init(-1, NULL);
    ir->instr_idx = -1;
    ir->ir = NULL;
    ir->idom = NULL;
    return ir;
}

__weak_unused static bool is_no_result(struct ir_node *ir)
{
    return
        ir->instr_idx ==   -1 &&
        ir->ir        == NULL &&
        ir->idom      == NULL;
}

static inline bool is_power_of_two(int32_t x)
{
    if (x <= 0) return 0;
    return (x & (x - 1)) == 0;
}

static inline int32_t nth_bit(int32_t x)
{
    assert(is_power_of_two(x));

    int32_t idx = 0;

    while (x > 0) {
        if (x & 1) return idx;
        x >>= 1;
        ++idx;
    }

    weak_unreachable("Expected power of 2 as input, got %d.", x);
}

#define __match(__op, l, r) \
    (bin->op == __op && lhs->type == l && rhs->type == r)

static struct ir_node *opt_arith_bin(struct ir_bin *bin)
{
    struct ir_node *lhs = bin->lhs;
    struct ir_node *rhs = bin->rhs;

    /// x - x = 0
    if (__match(TOK_MINUS, IR_SYM, IR_SYM)) {
        struct ir_sym *l_sym = lhs->ir;
        struct ir_sym *r_sym = rhs->ir;

        if (l_sym->idx == r_sym->idx) {
            return ir_imm_int_init(0);
        }
    }

    /// x + 0 = x
    if (__match(TOK_PLUS, IR_SYM, IR_IMM)) {
        struct ir_sym *l_sym = lhs->ir;
        struct ir_imm *r_imm = rhs->ir;

        if (r_imm->imm.__int == 0)
            return ir_sym_init(l_sym->idx);
    }

    /// x - 0 = x
    if (__match(TOK_MINUS, IR_SYM, IR_IMM)) {
        struct ir_sym *l_sym = lhs->ir;
        struct ir_imm *r_imm = rhs->ir;

        if (r_imm->imm.__int == 0)
            return ir_sym_init(l_sym->idx);
    }

    /// x * 0 = 0
    if (__match(TOK_STAR, IR_SYM, IR_IMM)) {
        struct ir_imm *r_imm = rhs->ir;

        if (r_imm->imm.__int == 0)
            return ir_imm_int_init(0);
    }

    /// x & 0 = 0
    if (__match(TOK_BIT_AND, IR_SYM, IR_IMM)) {
        struct ir_imm *r_imm = rhs->ir;

        if (r_imm->imm.__int == 0)
            return ir_imm_int_init(0);
    }

    /// x | 0 = x
    if (__match(TOK_BIT_OR, IR_SYM, IR_IMM)) {
        struct ir_sym *l_sym = lhs->ir;
        struct ir_imm *r_imm = rhs->ir;

        if (r_imm->imm.__int == 0)
            return ir_sym_init(l_sym->idx);
    }

    /// x * (power of 2) = x << (n'th bit)
    if (__match(TOK_STAR, IR_SYM, IR_IMM)) {
        struct ir_sym *l_sym = lhs->ir;
        struct ir_imm *r_imm = rhs->ir;

        if (is_power_of_two(r_imm->imm.__int))
            return ir_bin_init(
                TOK_SHL,
                ir_sym_init(l_sym->idx),
                ir_imm_int_init(nth_bit(r_imm->imm.__int))
            );
    }

    return no_result();
}

static void opt_arith_store(struct ir_store *store)
{
    if (store->body->type != IR_BIN) return;
    // if (store->type != IR_STORE_BIN) return;

    struct ir_node *node = opt_arith_node(store->body);

    if (is_no_result(node)) return;

    ir_node_cleanup(store->body);
    store->body = node;

    // switch (node->type) {
    // case IR_BIN:
    //     store->type = IR_STORE_BIN;
    //     break;
    // case IR_IMM:
    //     store->type = IR_STORE_IMM;
    //     break;
    // case IR_SYM:
    //     store->type = IR_STORE_SYM;
    //     break;
    // default:
    //     break;
    // }
}

static void opt_arith_ret(struct ir_ret *ret)
{
    if (ret->is_void)
        return;

    struct ir_node *body = opt_arith_node(ret->body);

    if (!is_no_result(body)) {
        ir_node_cleanup(ret->body);
        ret->body = body;
    }
}

static struct ir_node *opt_arith_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_JUMP:
    case IR_MEMBER:
    case IR_TYPE_DECL:
    case IR_FUNC_DECL:
    case IR_FUNC_CALL:
    case IR_ALLOCA:
    case IR_IMM:
    case IR_SYM:
        break;
    case IR_STORE:
        opt_arith_store(ir->ir);
        break;
    case IR_BIN:
        return opt_arith_bin(ir->ir);
    case IR_RET:
    case IR_RET_VOID:
        opt_arith_ret(ir->ir);
        break;
    case IR_COND:
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }

    return no_result();
}

/// Transform arithmetic operations.
///
///     1. Negation laws:
///        - A - (-B) = A + B
///        -(-A) = A
///
///     2. Double negation laws:
///        - ~(~A) = A
///
///     3. Bitwise complement laws:
///        - ~A + 1 = -A
///        - ~(-A) - 1 = A
///
///     4. Zero laws:
///        - A + 0 = A
///        - A - 0 = A
///        - A * 0 = 0
///        - A & 0 = 0
///        - A | 0 = A
///
///     5. Identity laws:
///        - A + (-A) = 0
///        - A - A = 0
///        - A * 1 = A
///        - A & 1 = A
///        - A | 1 = 1
///
///     6. De Morgan's laws:
///        - ~(A & B) = ~A | ~B
///        - ~(A | B) = ~A & ~B
///
///     7. Distributive laws:
///        - A * (B + C) = (A * B) + (A * C)
///        - A + (B * C) = (A + B) * (A + C)
///
///     8. Associative laws:
///        - (A + B) + C = A + (B + C)
///        - (A * B) * C = A * (B * C)
///
///     9. Commutative laws:
///        - A + B = B + A
///        - A * B = B * A
///        - A & B = B & A
///        - A | B = B | A
void ir_opt_arith(struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;
    while (it) {
        opt_arith_node(it);
        it = it->next;
    }
}