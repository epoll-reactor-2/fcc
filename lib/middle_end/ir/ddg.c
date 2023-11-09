/* ddg.c - Data dependence graph.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ddg.h"
#include "middle_end/ir/ir.h"
#include "util/hashmap.h"
#include <assert.h>

/* Key:   ir
   Value: sym_idx */
static hashmap_t stores;



static void ddg_add_dependency(struct ir_node *ir, struct ir_node *symbol)
{
    if (symbol->type != IR_SYM) return;

    struct ir_sym *sym = symbol->ir;

    hashmap_foreach(&stores, k, v) {
        if (v == (uint64_t) sym->idx) {
            struct ir_node *node = (struct ir_node *) k;
            vector_push_back(ir->ddg_stmts, node);
        }
    }
}

static void ddg_bin(struct ir_node *ir, struct ir_node *ir_bin)
{
    struct ir_bin *bin = ir_bin->ir;

    ddg_add_dependency(ir, bin->lhs);
    ddg_add_dependency(ir, bin->rhs);
}

static void ddg_node(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA: {
        struct ir_alloca *alloca = ir->ir;
        hashmap_put(&stores, (uint64_t) ir, alloca->idx);
        break;
    }
    case IR_STORE: {
        struct ir_store *store = ir->ir;
        if (store->idx->type == IR_SYM) {
            struct ir_sym *sym = store->idx->ir;
            hashmap_put(&stores, (uint64_t) ir, sym->idx);
        }

        if (store->body->type == IR_BIN)
            ddg_bin(ir, store->body);

        if (store->body->type == IR_SYM)
            ddg_add_dependency(ir, store->body);

        break;
    }
    case IR_COND: {
        struct ir_cond *cond = ir->ir;
        assert(cond->cond->type == IR_BIN);
        ddg_bin(ir, cond->cond);
        break;
    }
    case IR_RET: {
        struct ir_ret *ret = ir->ir;
        if (!ret->is_void && ret->body->type == IR_SYM)
            ddg_add_dependency(ir, ret->body);
        break;
    }
    default:
        break;
    }
}

static void ddg_cleanup(struct ir_node *ir)
{
    struct ir_node *it = ir;

    while (it) {
        vector_clear(it->ddg_stmts);
        it = it->next;
    }
}

static int qsort_cmp(const void *lhs, const void *rhs)
{
    struct ir_node *l = *((struct ir_node **) lhs);
    struct ir_node *r = *((struct ir_node **) rhs);

    return l->instr_idx - r->instr_idx;
}

static void ddg_sort(struct ir_node *ir)
{
    ir_vector_t *ddgs = &ir->ddg_stmts;
    qsort(ddgs->data, ddgs->count, sizeof (struct ir_node *), qsort_cmp);
}

void ir_ddg_build(struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;

    hashmap_reset(&stores, 512);

    ddg_cleanup(it);

    while (it) {
        ddg_node(it);
        it = it->next;
    }

    it = decl->body;
    while (it) {
        ddg_sort(it);
        it = it->next;
    }

    __weak_debug({
        it = decl->body;

        while (it) {
            printf("For instr %ld, Required by = (", it->instr_idx);
            vector_foreach(it->ddg_stmts, i) {
                struct ir_node *stmt = vector_at(it->ddg_stmts, i);
                printf("%ld ", stmt->instr_idx);
            }
            printf(")\n");
            it = it->next;
        }
    });

    hashmap_destroy(&stores);
}