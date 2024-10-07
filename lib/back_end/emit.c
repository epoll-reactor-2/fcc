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

/* key:   CRC-32 name of a function
   value: .text offset */
static hashmap_t mapping_fn;
/* key:   CRC-32 name of a variable
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

struct tmp_reg {
    int reg;
    int busy;
};

static struct tmp_reg __tmp_reg_1 = { .reg = risc_v_reg_t0, /* busy */ 0 };
static struct tmp_reg __tmp_reg_2 = { .reg = risc_v_reg_t1, /* busy */ 0 };

static struct tmp_reg *__tmp_reg_active;

static struct tmp_reg *select_tmp_reg()
{
         if (!__tmp_reg_1.busy) { __tmp_reg_active = &__tmp_reg_1; }
    else if (!__tmp_reg_2.busy) { __tmp_reg_active = &__tmp_reg_2; }
    else
        weak_fatal_error("No free registers.");

    return __tmp_reg_active;
}

static void visit_imm(struct ir_imm *ir)
{
    switch (ir->type) {
    case IMM_INT:
        back_end_native_li(select_tmp_reg()->reg, ir->imm.__int);
        break;
    case IMM_BOOL:
    case IMM_FLOAT:
    case IMM_CHAR:
    default:
        break;
    }
}

static void visit_ret(unused struct ir_ret *ir)
{
    if (ir->body)
        visit(ir->body);

    back_end_native_addi(back_end_return_reg(), __tmp_reg_active->reg, 0);
}

static void visit_store(struct ir_store *ir)
{
    visit(ir->body);
}

static void visit_chain(struct ir_node *ir)
{
    while (ir) {
        visit(ir);
        ir = ir->next;
    }
}

static void visit_fn_main(unused struct ir_fn_decl *ir)
{
    visit_chain(ir->body);

    // back_end_native_addi(risc_v_reg_a0, __tmp_reg_active);
    back_end_native_syscall_0(__NR_exit);
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

    visit_chain(ir->body);

    back_end_native_epilogue(stack_usage);
    back_end_native_ret();
}

/* _start must be located at the start address
   and perform jump to main.

   For now it contains only one instruction,
   but will be useful to make generic API. */
static uint64_t _start_size  = 0x04;
/* This is setup before `main` code generation
   in order to jump from _start. */
static uint64_t main_seek    = 0x00;
static bool     main_emitted = 0;

static void visit_fn_call(struct ir_fn_call *ir)
{
    uint64_t crc = crc32_string(ir->name);
    bool     ok  = 0;
    uint64_t off = hashmap_get(&mapping_fn, crc, &ok);

    if (!ok)
        weak_fatal_error("Cannot find `%s` function.", ir->name);

    uint64_t call_off = off - back_end_seek();
    if (!main_emitted)
        /* main() is implemented as `jal <main-offset>`.
           At this moment we generating functions before main
           so we pre-calculate size of _start function and
           substract this.

           After main() is generated, our seek is aligned to
           real value with _start offset. */
        call_off -= _start_size;

    back_end_native_call(call_off);
}

static void visit_fn_decl(struct ir_fn_decl *ir)
{

    uint64_t crc = crc32_string(ir->name);

    if (!strcmp(ir->name, "main")) {
        main_emitted = 1;

        main_seek = back_end_seek() + _start_size;
        back_end_emit_sym(ir->name, main_seek);

        uint64_t seek = back_end_seek() + _start_size;

        hashmap_put(&mapping_fn, crc, main_seek);

        back_end_seek_set(0);
        back_end_native_call(main_seek);
        back_end_seek_set(seek);

        visit_fn_main(ir);
    } else {
        /* Where `main()` is generated, we don't need
           to play with additional _start function
           offset and it is correct without it now. */
        uint64_t off = main_emitted
            ? back_end_seek()
            : back_end_seek() + _start_size;

        back_end_emit_sym(ir->name, off);
        hashmap_put(&mapping_fn, crc, off);
        visit_fn_usual(ir);
    }
}

static void visit(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:       visit_alloca(ir->ir); break;
    case IR_ALLOCA_ARRAY: /* visit_alloca_array(ir->ir); */ break;
    case IR_IMM:          visit_imm(ir->ir); break;
    case IR_STRING:       /* visit_string(ir->ir); */ break;
    case IR_SYM:          /* visit_sym(ir); */ break;
    case IR_STORE:        visit_store(ir->ir); break;
    case IR_PUSH:         /* visit_push(ir->ir); */ break;
    case IR_POP:          /* visit_pop(ir->ir); */ break;
    case IR_BIN:          /* visit_bin(ir->ir); */ break;
    case IR_JUMP:         /* visit_jump(ir->ir); */ break;
    case IR_COND:         /* visit_cond(ir->ir); */ break;
    case IR_RET:          visit_ret(ir->ir); break;
    case IR_MEMBER:       /* visit_member(ir->ir); */ break;
    case IR_TYPE_DECL:    /* visit_type_decl(ir->ir); */ break;
    case IR_FN_DECL:      /* visit_fn_decl(ir->ir); */ break;
    case IR_FN_CALL:      visit_fn_call(ir->ir); break;
    case IR_PHI:          /* visit_phi(ir->ir); */ break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}

void back_end_gen(struct ir_unit *unit)
{
    hashmap_init(&mapping_fn, 32);
    hashmap_init(&mapping, 32);
    hashmap_init(&mapping_type, 32);

    back_end_emit_sym("_start", back_end_seek());

    struct ir_node *it = unit->fn_decls;
    while (it) {
        visit_fn_decl(it->ir);
        it = it->next;
    }
}