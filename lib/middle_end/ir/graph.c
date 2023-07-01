/* graph.c - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/graph.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ir.h"

void ir_link(struct ir *ir)
{
    for (uint64_t j = 0; j < ir->decls_size; ++j) {
        struct ir_func_decl *decl = ir->decls[j].ir;

        for (uint64_t i = 0; i < decl->body_size - 1; ++i) {
            struct ir_node *stmt = &decl->body[i    ];
            struct ir_node *next = &decl->body[i + 1];
            switch (stmt->type) {
            case IR_IMM:
            case IR_SYM:
            case IR_BIN:
            case IR_MEMBER:
            case IR_ARRAY_ACCESS:
                break;
            case IR_STORE: {
                struct ir_store *store = stmt->ir;
                store->next = next;
                break;
            }
            case IR_LABEL: {
                struct ir_label *label = stmt->ir;
                label->next = next;
                break;
            }
            case IR_JUMP: {
                struct ir_jump *jump = stmt->ir;
                jump->next = &decl->body[jump->idx];
                break;
            }
            case IR_COND: {
                struct ir_cond *cond = stmt->ir;
                cond->next_true = &decl->body[cond->goto_label];
                cond->next_false = next;
                break;
            }
            case IR_RET: {
                struct ir_ret *ret = stmt->ir;
                if (i <= decl->body_size - 1)
                    ret->next = next;
                break;
            }
            case IR_RET_VOID: {
                struct ir_ret *ret = stmt->ir;
                if (i <= decl->body_size - 1)
                    ret->next = next;
                break;
            }
            case IR_ALLOCA: {
                struct ir_alloca *alloca = stmt->ir;
                alloca->next = next;
                break;
            }
            case IR_FUNC_CALL: {
                struct ir_func_call *call = stmt->ir;
                call->next = next;
                break;
            }
            default:
                break;
            }
        }
    }
}

static void ir_dom_tree_func_decl(struct ir_func_decl *decl)
{
    struct ir_node *root           = &decl->body[0];
    struct ir_node *worklist[2048] = {0};
    uint64_t        siz            =  0;

    root->idom = root;

    worklist[siz++] = root;

    while (siz > 0) {
        struct ir_node *cur = worklist[--siz];

        switch (cur->type) {
        case IR_IMM:
        case IR_SYM:
        case IR_BIN:
        case IR_MEMBER:
        case IR_ARRAY_ACCESS:
            break;
        case IR_STORE: {
            /// Note:
            /// Each store variable is dominated by their declarations
            /// in the CFG. However, if there will appear some logical errors,
            /// this place should be reviewed and verified, if variable indices
            /// inside the store instructions are properly dominated.
            ///
            /// alloca int %1
            /// ...
            /// store %1 %N
            struct ir_store *store = cur->ir;
            struct ir_node  *succ  = store->next;
            if (succ->idom == NULL) {
                succ->idom = cur;
                worklist[siz++] = succ;
            }
            break;
        }
        case IR_LABEL: {
            struct ir_label *label = cur->ir;
            struct ir_node  *succ  = label->next;
            if (succ->idom == NULL) {
                succ->idom = cur;
                worklist[siz++] = succ;
            }
            break;
        }
        case IR_JUMP: {
            struct ir_jump *jump = cur->ir;
            struct ir_node *succ = jump->next;
            if (succ->idom == NULL) {
                succ->idom = cur;
                worklist[siz++] = succ;
            }
            break;
        }
        case IR_COND: {
            struct ir_cond *cond  = cur->ir;
            struct ir_node *succ1 = cond->next_true;
            struct ir_node *succ2 = cond->next_false;
            if (succ1->idom == NULL) {
                succ1->idom = cur;
                worklist[siz++] = succ1;
            }
            if (succ2->idom == NULL) {
                succ2->idom = cur;
                worklist[siz++] = succ2;
            }
            break;
        }
        case IR_RET: {
            struct ir_ret  *ret  = cur->ir;
            struct ir_node *succ = ret->next;
            if (ret->next) {
                if (succ->idom == NULL) {
                    succ->idom = cur;
                    worklist[siz++] = succ;
                }
            }
            break;
        }
        case IR_RET_VOID: {
            struct ir_ret  *ret  = cur->ir;
            struct ir_node *succ = ret->next;
            if (ret->next) {
                if (succ->idom == NULL) {
                    succ->idom = cur;
                    worklist[siz++] = succ;
                }
            }
            break;
        }
        case IR_ALLOCA: {
            struct ir_alloca *alloca = cur->ir;
            struct ir_node   *succ   = alloca->next;
            if (succ->idom == NULL) {
                succ->idom = cur;
                worklist[siz++] = succ;
            }
            break;
        }
        case IR_FUNC_CALL: {
            struct ir_func_call *call = cur->ir;
            struct ir_node      *succ = call->next;
            if (succ->idom == NULL) {
                succ->idom = cur;
                worklist[siz++] = succ;
            }
            break;
        }
        default:
            break;
        }
    }
}

void ir_compute_dom_tree(struct ir *ir)
{
    for (uint64_t j = 0; j < ir->decls_size; ++j) {
        struct ir_func_decl *decl = ir->decls[j].ir;
        ir_dom_tree_func_decl(decl);
    }
}

/*
Steck' ein Messer in mein Bein und es kommt Blut raus
Doch die Schmerzen gehen vorbei
Meine Schwestern schreiben: „Bro, du siehst nicht gut aus“
Kann schon sein, weil ich bin high
*/