/* arith.c - Arithmetic operations transform.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/opt/opt.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ir.h"
#include "util/unreachable.h"

static struct ir_node opt_arith_node(struct ir_node *ir);

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

static struct ir_node opt_arith_bin(struct ir_bin *bin)
{
    struct ir_node *lhs = &bin->lhs;
    struct ir_node *rhs = &bin->rhs;

    printf("\nLHS type: %d, RHS type: %d\n", lhs->type, rhs->type);
    printf("Type: %s\n", tok_to_string(bin->op));

    if (lhs->type == IR_SYM && rhs->type == IR_SYM) {
        struct ir_sym *l_sym = lhs->ir;
        struct ir_sym *r_sym = rhs->ir;

        if (bin->op == TOK_MINUS) {
            printf("LHS sym: %d, RHS sym: %d\n", l_sym->idx, r_sym->idx);
            if (l_sym->idx == r_sym->idx) {
                puts("Both symbols");
                return ir_imm_int_init(0);
            }
        }
    }

    return no_result();
}

static void opt_arith_store(struct ir_store *store)
{
    if (store->type != IR_STORE_BIN) return;

    puts("Store arg");
    ir_dump_node(stdout, &store->body);

    struct ir_node node = opt_arith_node(&store->body);

    if (!is_no_result(&node)) {
        ir_node_cleanup(store->body);
        store->body = node;
        store->type = IR_STORE_IMM;
    }
}

static void opt_arith_ret(struct ir_ret *ret)
{
    if (ret->is_void)
        return;

    struct ir_node body = opt_arith_node(&ret->op);

    if (!is_no_result(&body)) {
        ir_node_cleanup(ret->op);
        ret->op = body;
    }
}

static struct ir_node opt_arith_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_LABEL:
    case IR_JUMP:
    case IR_MEMBER:
    case IR_ARRAY_ACCESS:
    case IR_TYPE_DECL:
    case IR_FUNC_DECL:
    case IR_FUNC_CALL:
    case IR_ALLOCA:
    case IR_IMM:
    case IR_SYM:
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

static void opt_arith(struct ir_func_decl *decl)
{
    for (uint64_t i = 0; i < decl->body_size; ++i) {
        struct ir_node *node = &decl->body[i];
        opt_arith_node(node);
    }
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
void ir_opt_arith(struct ir *ir)
{
    for (uint64_t i = 0; i < ir->decls_size; ++i) {
        struct ir_func_decl *decl = ir->decls[i].ir;
        opt_arith(decl);
    }
}