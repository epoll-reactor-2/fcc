/* eval.c - Weak language IR interpreter.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/eval.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/dump.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include <assert.h>
#include <string.h>

/// Key:   variable index
/// Value: its value
static hashmap_t stack;
static struct ir_imm last;
static int32_t exit_code;

static struct ir_node *jmp_target;
static hashmap_t jmp_table;

static struct ir_node *jmp_table_get(int32_t instr_idx)
{
    bool ok = 0;
    uint64_t got = hashmap_get(&jmp_table, instr_idx, &ok);
    if (!ok)
        weak_unreachable("Cannot get %%%d from jump table", instr_idx);    

    return (struct ir_node *) got;
}

static void jmp_table_init(struct ir_node *ir)
{
    struct ir_node *it = ir;
    while (it) {
        hashmap_put(&jmp_table, it->instr_idx, (uint64_t) it);
        it = it->next;
    }
}

static void reset_hashmap(hashmap_t *map)
{
    if (map->buckets) {
        hashmap_destroy(map);
    }
    hashmap_init(map, 512);
}

static void reset()
{
    reset_hashmap(&stack);
    reset_hashmap(&jmp_table);

    memset(&last, 0, sizeof last);
    exit_code = 0;
    jmp_target = NULL;
}

static void stack_push(int32_t idx)
{
    /// Even if after optimization some
    /// variables will have no store instruction,
    /// (be uninitialized), they will be set to 0.
    hashmap_put(&stack, idx, (uint64_t) 0);
}

static void stack_set(int32_t idx, union ir_imm_val imm)
{
    __weak_debug({
        bool ok = 0;
        hashmap_get(&stack, idx, &ok);
        if (!ok)
            weak_unreachable("Cannot get stack entry %%%d", idx);        
    });
    hashmap_put(&stack, idx, (uint64_t) imm.__int);
}

static union ir_imm_val stack_get(int32_t idx)
{
    bool ok = 0;
    uint64_t got = hashmap_get(&stack, idx, &ok);
    assert(ok && "Stack have no requested entry.");
    return (union ir_imm_val) (int32_t) got;
}

static void eval_fun(struct ir_func_decl *decl);
static void eval_instr(struct ir_node *ir);

static void eval_alloca(struct ir_alloca *alloca)
{
    stack_push(alloca->idx);
}

static void eval_imm(struct ir_imm *imm)
{
    last = *imm;
}

static void eval_sym(struct ir_sym *sym)
{
    union ir_imm_val imm_val = stack_get(sym->idx);

    struct ir_imm imm = {
        .type = IMM_INT,
        .imm  = imm_val
    };

    last = imm;
}

static void eval_store_bin(struct ir_store *ir)
{
    eval_instr(ir->body);
    stack_set(ir->idx, last.imm);
}

static void eval_store_imm(struct ir_store *ir)
{
    struct ir_imm *imm = ir->body->ir;
    stack_set(ir->idx, imm->imm);
}

static void eval_store_sym(struct ir_store *ir)
{
    struct ir_sym *sym = ir->body->ir;
    union ir_imm_val imm = stack_get(sym->idx);
    stack_set(ir->idx, imm);
}

static void eval_store(struct ir_store *ir)
{
    switch (ir->type) {
    case IR_STORE_BIN: {
        eval_store_bin(ir);
        break;
    }
    case IR_STORE_SYM: {
        eval_store_sym(ir);
        break;
    }
    case IR_STORE_IMM: {
        eval_store_imm(ir);
        break;
    }
    default:
        break;
    }
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

static struct ir_imm eval_imm_imm_int(enum token_type op, int32_t l, int32_t r)
{
    /// \todo: Char.
    struct ir_imm imm = {
        .type = IMM_INT,
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
    case IMM_BOOL:  return eval_imm_imm_bool (op, l.imm.__bool,  r.imm.__bool);
    case IMM_CHAR:  return eval_imm_imm_int  (op, l.imm.__char,  r.imm.__char);
    case IMM_FLOAT: return eval_imm_imm_float(op, l.imm.__float, r.imm.__float);
    case IMM_INT:   return eval_imm_imm_int  (op, l.imm.__int,   r.imm.__int);
    default:
        weak_unreachable("Unknown immediate type (numeric: %d).", l.type);        
    }
}

static void eval_bin(struct ir_bin *ir)
{
    eval_instr(ir->lhs);
    struct ir_imm l = last;

    eval_instr(ir->rhs);
    struct ir_imm r = last;

    last = eval_imm_imm(ir->op, l, r);
}

static void eval_ret(struct ir_ret *ir)
{
    if (ir->is_void)
        exit_code = -1;

    eval_instr(ir->body);
    exit_code = last.imm.__int;
}

static void eval_cond(struct ir_cond *cond)
{
    eval_instr(cond->cond);

    bool should_jump = 0;
    switch (last.type) {
    case IMM_BOOL:  should_jump = last.imm.__bool; break;
    case IMM_CHAR:  should_jump = last.imm.__char != 0.0; break;  
    case IMM_FLOAT: should_jump = last.imm.__float != 0.0; break;
    case IMM_INT:   should_jump = last.imm.__int != 0; break;
    default:
        weak_unreachable("Unknown immediate type (numeric: %d).", last.type);
    }

    if (should_jump)
        jmp_target = jmp_table_get(cond->goto_label)->prev;
}

static void eval_jmp(struct ir_jump *jmp)
{
    /// Prev is due eval_fun() execution loop specific algorithm.
    jmp_target = jmp_table_get(jmp->idx)->prev;
}

static void eval_instr(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        eval_alloca(ir->ir);
        break;
    case IR_IMM:
        eval_imm(ir->ir);
        break;
    case IR_SYM:
        eval_sym(ir->ir);
        break;
    case IR_LABEL:
        break;
    case IR_JUMP:
        eval_jmp(ir->ir);
        break;
    case IR_MEMBER:
    case IR_ARRAY_ACCESS:
    case IR_TYPE_DECL:
        break;
    case IR_FUNC_DECL:
        eval_fun(ir->ir);
        break;
    case IR_FUNC_CALL:
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

static void eval_fun(struct ir_func_decl *decl)
{
    reset();

    struct ir_node *it = decl->body;
    jmp_table_init(it);

    jmp_target = it;

    while (jmp_target) {
        eval_instr(jmp_target);
        jmp_target = jmp_target->next;
    }
}

int32_t eval(struct ir_node *ir)
{
    struct ir_node *it = ir;
    while (it) {
        eval_fun(it->ir);
        it = it->next;
    }

    return exit_code;
}