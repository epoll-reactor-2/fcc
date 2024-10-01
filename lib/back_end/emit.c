/* emit.c - Code generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/emit.h"
#include "back_end/back_end.h"

/*** Temporary ***/
#include "back_end/risc_v.h"
/***           ***/

#include "middle_end/ir/ir.h"
#include "util/compiler.h"
#include "util/hashmap.h"
#include "util/crc32.h"
#include "util/unreachable.h"
#include <stdbool.h>
#include <string.h>
#include <asm-generic/unistd.h>

/**********************************************
 * Variable mapping                           *
 **********************************************/

/* How much stack space is occupied by
   variables. */
static uint64_t stack_off;

/* key:   CRC-32 name
   value: stack offset */
static hashmap_t mapping;
/* key:   CRC-32 name
   value: type */
static hashmap_t mapping_type;

/**********************************************
 * Codegen                                    *
 **********************************************/

static uint64_t offset_of(uint64_t alloca_idx)
{
    bool     ok  = 0;
    uint64_t off = hashmap_get(&mapping, alloca_idx, &ok);

    if (!ok)
        weak_fatal_error("Cannot get stack offset for `t%lu`\n", alloca_idx);

    return off;
}

static void visit(struct ir_node *ir);

static void visit_alloca(struct ir_alloca *ir)
{
    uint64_t size = data_type_size[ir->dt];

    hashmap_put(&mapping, ir->idx, stack_off);
    hashmap_put(&mapping_type, ir->idx, ir->dt);

    printf("Allocating t%lu at offset %lu\n", ir->idx, offset_of(ir->idx));

    stack_off += size;
}

static void visit(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:       visit_alloca(ir->ir); break;
    case IR_ALLOCA_ARRAY: /* _alloca_array(ir->ir); */ break;
    case IR_IMM:          /* _imm(ir->ir); */ break;
    case IR_STRING:       /* _string(ir->ir); */ break;
    case IR_SYM:          /* _sym(ir); */ break;
    case IR_STORE:        /* _store(ir->ir); */ break;
    case IR_PUSH:         /* _push(ir->ir); */ break;
    case IR_POP:          /* _pop(ir->ir); */ break;
    case IR_BIN:          /* _bin(ir->ir); */ break;
    case IR_JUMP:         /* _jump(ir->ir); */ break;
    case IR_COND:         /* _cond(ir->ir); */ break;
    case IR_RET:          /* _ret(ir->ir); */ break;
    case IR_MEMBER:       /* _member(ir->ir); */ break;
    case IR_TYPE_DECL:    /* _type_decl(ir->ir); */ break;
    case IR_FN_DECL:      /* _fn_decl(ir->ir); */ break;
    case IR_FN_CALL:      /* _fn_call(ir->ir); */ break;
    case IR_PHI:          /* _phi(ir->ir); */ break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}

static void visit_fn_main(unused struct ir_fn_decl *ast)
{
    back_end_native_syscall_1(__NR_exit, 42);
}

static void visit_fn_usual(unused struct ir_fn_decl *ir)
{
    /* TODO: Calculate how much variables are allocated
             in function.

             This codegen assumed to compute variable
             values using temporary registers and
             store value to variable via stack.

             Variable is also must be referred only
             by stack. */
    int stack_usage = 0;

    back_end_native_prologue(stack_usage);
    // visit(ast->body);

    struct ir_node *it = ir->body;
    while (it) {
        visit(it);
        it = it->next;
    }

    back_end_native_epilogue(stack_usage);
    back_end_native_ret();
}

/* _start must be located at the start address
   and perform jump to main.

   For now it contains only one instruction,
   but will be useful to make generic API. */
static uint64_t _start_size = 0x04;
/* This is setup before `main` code generation
   in order to jump from _start. */
static uint64_t main_seek   = 0x00;

static void visit_fn_decl(struct ir_fn_decl *ir)
{
    static bool main_emitted = 0;

    if (!strcmp(ir->name, "main")) {
        main_seek = back_end_seek() + _start_size;
        back_end_emit_sym(ir->name, main_seek);
        visit_fn_main(ir);

        uint64_t seek = back_end_seek() + _start_size;

        back_end_seek_set(0);
        back_end_native_call(main_seek);
        back_end_seek_set(seek);

        main_emitted = 1;
    } else {
        /* Where `main()` is generated, we don't need
           to play with additional _start function
           offset and it is correct without it now. */
        uint64_t off = main_emitted
            ? back_end_seek()
            : back_end_seek() + _start_size;

        back_end_emit_sym(ir->name, off);
        visit_fn_usual(ir);
    }
}

void back_end_gen(struct ir_unit *unit)
{
    hashmap_init(&mapping, 32);
    hashmap_init(&mapping_type, 32);

    back_end_emit_sym("_start", back_end_seek());

    struct ir_node *it = unit->fn_decls;
    while (it) {
        visit_fn_decl(it->ir);
        it = it->next;
    }
}