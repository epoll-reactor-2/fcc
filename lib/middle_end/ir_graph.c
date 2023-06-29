/* ir_graph.c - Functions to build graph from IR.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_graph.h"
#include "middle_end/ir_dump.h"
#include "middle_end/ir.h"
#include <stdio.h>
#include <stdlib.h>

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

/*
Steck' ein Messer in mein Bein und es kommt Blut raus
Doch die Schmerzen gehen vorbei
Meine Schwestern schreiben: „Bro, du siehst nicht gut aus“
Kann schon sein, weil ich bin high
*/