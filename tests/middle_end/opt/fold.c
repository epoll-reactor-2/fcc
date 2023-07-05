/* fold.c - Test cases for constant folding.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/gen.h"
#include "middle_end/opt/opt.h"
#include "util/compiler.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void ir_cmp_nodes(struct ir_node *lhs, struct ir_node *rhs)
{
    if (lhs->type != rhs->type)
        ASSERT_TRUE(0 && "Type mismatch");

    switch (lhs->type) {
    case IR_ALLOCA: {
        struct ir_alloca *l = lhs->ir;
        struct ir_alloca *r = rhs->ir;
        ASSERT_TRUE(
            l->dt == r->dt &&
            l->idx == r->idx
        );
        break;
    }
    case IR_IMM: {
        struct ir_imm *l = lhs->ir;
        struct ir_imm *r = rhs->ir;
        ASSERT_TRUE(l->type == r->type);
        switch (l->type) {
        case IMM_BOOL:
            ASSERT_TRUE(l->imm_bool == r->imm_bool);
            break;
        case IMM_CHAR:
            ASSERT_TRUE(l->imm_char == r->imm_char);
            break;
        case IMM_FLOAT:
            ASSERT_TRUE(l->imm_float == r->imm_float);
            break;
        case IMM_INT:
            ASSERT_TRUE(l->imm_int == r->imm_int);
            break;
        default:
            break;
        }
        break;
    }
    case IR_SYM: {
        struct ir_sym *l = lhs->ir;
        struct ir_sym *r = rhs->ir;
        ASSERT_TRUE(l->idx == r->idx);
        break;
    }
    case IR_LABEL: {
        struct ir_label *l = lhs->ir;
        struct ir_label *r = rhs->ir;
        ASSERT_TRUE(l->idx == r->idx);
        break;
    }
    case IR_JUMP: {
        struct ir_jump *l = lhs->ir;
        struct ir_jump *r = rhs->ir;
        ASSERT_TRUE(l->idx == r->idx);
        break;
    }
    case IR_STORE: {
        struct ir_store *l = lhs->ir;
        struct ir_store *r = rhs->ir;
        ASSERT_TRUE(l->type == r->type);
        ir_cmp_nodes(&l->body, &r->body);
        break;
    }
    case IR_BIN: {
        struct ir_bin *l = lhs->ir;
        struct ir_bin *r = rhs->ir;
        ASSERT_TRUE(l->op == r->op);
        ir_cmp_nodes(&l->lhs, &r->lhs);
        ir_cmp_nodes(&l->rhs, &r->rhs);
        break;
    }
    case IR_COND: {
        struct ir_cond *l = lhs->ir;
        struct ir_cond *r = rhs->ir;
        ASSERT_TRUE(l->goto_label == r->goto_label);
        ir_cmp_nodes(&l->cond, &r->cond);
        break;
    }
    case IR_RET:
    case IR_RET_VOID: {
        struct ir_ret *l = lhs->ir;
        struct ir_ret *r = rhs->ir;
        ASSERT_TRUE(l->is_void == r->is_void);
        ir_cmp_nodes(&l->op, &r->op);
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

void ir_cmp(
    struct ir_node *converted,
    uint64_t        converted_siz,
    struct ir_node *assert,
    uint64_t        assert_siz
) {
    if (converted_siz != assert_siz)
        ASSERT_TRUE(0 && "Size mismatch");
    
    for (uint64_t i = 0; i < assert_siz; ++i) {
        struct ir_node *lhs = &converted[i];
        struct ir_node *rhs = &assert[i];
        ir_cmp_nodes(lhs, rhs);
    }
}

void test_fold(
    struct ir_node *src,
    uint64_t        src_siz,
    struct ir_node *assert,
    uint64_t        assert_siz
) {
    struct ir_node decl = ir_func_decl_init(
        /*name=*/      "f",
        /*args_size=*/ 0,
        /*args=*/      NULL,
        /*body_size=*/ src_siz,
        /*body=*/      src
    );

    (void) assert;
    (void) assert_siz;

    ir_dump_node(stdout, &decl);
    puts("");

    struct ir ir = {
        .decls      = &decl,
        .decls_size = 1
    };

    ir_opt_fold(&ir);

    ir_dump_node(stdout, &decl);
    puts("");

    ir_cmp(src, src_siz, assert, assert_siz);
}

#define _ALLOCA(type, ir) ir_alloca_init(type, ir)
#define _IMM_B(x)         ir_imm_bool_init(x)
#define _IMM_C(x)         ir_imm_char_init(x)
#define _IMM_F(x)         ir_imm_float_init(x)
#define _IMM_I(x)         ir_imm_int_init(x)
#define _SYM(x)           ir_sym_init(x)
#define _STORE_I(idx, x)  ir_store_imm_init(idx, x)
#define _STORE_V(idx, x)  ir_store_var_init(idx, x)
#define _STORE_B(idx, x)  ir_store_bin_init(idx, x)
#define _BIN(op, l, r)    ir_bin_init(op, l, r)
#define _LBL(idx)         ir_label_init(idx)
#define _JMP(idx)         ir_jump_init(idx)
#define _COND(body, jmp)  ir_cond_init(body, jmp)
#define _RET(is_void, op) ir_ret_init(is_void, op)

int main()
{
    struct ir_node ir[] = {
        _STORE_B(0, _BIN(TOK_PLUS, _IMM_I(1), _IMM_I(2))),
    };

    struct ir_node assert[] = {
        _STORE_I(0, _IMM_I(3)),
    };

    test_fold(
        ir,     __weak_array_size(ir),
        assert, __weak_array_size(assert)
    );
}