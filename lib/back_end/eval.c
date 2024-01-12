/* eval.c - Weak language IR interpreter.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/eval.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include "util/vector.h"
#include "execution.h"
#include <assert.h>
#include <string.h>



#define STACK_SIZE_BYTES 32768

/* ==========================
   Stack routines.
   ========================== */

/* sp -- stack pointer
   bp -- base pointer (callee-save) */

/* NOTE: Such stack usage has sense only with reordered alloca
         instructions, where they are all collected at the beginning of
         the function. Thus, we not require to injure our stack during
         loop execution. Each variable allocated once and set up
         multiple times.

         Moreover, language semantics forbid to have uninitialized
         values.

         Stack contains `struct value`. */
static char     stack[STACK_SIZE_BYTES];
/* Index: sym_idx
   Value: sp */
static char     stack_map[STACK_SIZE_BYTES];
/* Global stack pointer. Named as assembly register. */
static uint64_t sp;



static void reset()
{
    memset(stack_map, 0, sizeof (stack_map));
    memset(stack, 0, sizeof (stack));
    sp = 0;
}

/* Notice: There is no `pop` function, since popping
           is implemented by storing stack pointer before
           call and restoring it after call. */
static inline void push(uint64_t sym_idx, uint64_t imm_siz)
{
    stack_map[sym_idx] = sp;
    sp += imm_siz;
}

static inline void set(uint64_t sym_idx, struct value *v, struct type *traits)
{
    uint64_t sp_ptr = stack_map[sym_idx];

    /* __string is biggest union value. Rework this crap. */
    memcpy(&stack[sp_ptr], &v->__string, traits->bytes);
}

static inline void set_string(uint64_t sym_idx, char *imm)
{
    uint64_t sp_ptr = stack_map[sym_idx];
    strcpy(&stack[sp_ptr], imm);
}

static inline struct value get(uint64_t sym_idx, struct type *traits)
{
    uint64_t sp_ptr = stack_map[sym_idx];

    struct value v = {
        .dt = traits->dt
    };
    /* __string is biggest union value. Rework this crap. */
    memcpy(&v.__string, &stack[sp_ptr], traits->bytes);

    return v;
}



/* ==========================
   Instructions routines.
   ========================== */

static void call_eval(struct ir_fn_call *call);
static void instr_eval(struct ir_node *ir);

static struct ir_node *instr_ptr;
static struct value   last;



static uint64_t dt_size(enum data_type dt)
{
    switch (dt) {
    case D_T_BOOL:  return 1;
    case D_T_CHAR:  return 1;
    case D_T_INT:   return 4;
    case D_T_FLOAT: return 4;
    default:
        weak_unreachable("Unknown data type: `%s`", data_type_to_string(dt));
    }
}

static uint64_t alloca_size(struct ir_alloca *alloca)
{
    if (alloca->ptr_depth > 0)
        return 8;

    return dt_size(alloca->dt);
}

static uint64_t alloca_array_size(struct ir_alloca_array *alloca)
{
    uint64_t siz = 1;

    for (uint64_t i = 0; i < alloca->arity_size; ++i)
        siz *= alloca->arity[i];
    siz *= dt_size(alloca->dt);

    return siz;
}

static void eval_alloca(struct ir_alloca *alloca)
{
    uint64_t i     = alloca->idx;
    uint64_t bytes = alloca_size(alloca);

    push(i, bytes);
}

static void eval_alloca_array(struct ir_alloca_array *alloca)
{
    uint64_t i     = alloca->idx;
    uint64_t bytes = alloca_array_size(alloca);

    push(i, bytes);
}



static void eval_imm(struct ir_imm *imm)
{
    struct value v = {0};
    switch (imm->type) {
    case IMM_BOOL:  v.dt = D_T_BOOL;  v.__bool  = imm->imm.__bool;  break;
    case IMM_CHAR:  v.dt = D_T_CHAR;  v.__char  = imm->imm.__char;  break;
    case IMM_FLOAT: v.dt = D_T_FLOAT; v.__float = imm->imm.__float; break;
    case IMM_INT:   v.dt = D_T_INT;   v.__int   = imm->imm.__int;   break;
    default:
        weak_unreachable("Should not reach there.");
    }
    memcpy(&last, &v, sizeof (struct value));
}

static void eval_sym(struct ir_node *sym)
{
    struct ir_sym *s = sym->ir;
    struct type   *t = &s->type_info;
    struct value   v = get(s->idx, t);

    memcpy(&last, &v, sizeof(struct value));
}



static void eval_bools(enum token_type op, bool l, bool r)
{
    last.dt = D_T_BOOL;

    switch (op) {
    case TOK_BIT_AND: last.__bool = l & r; break;
    case TOK_BIT_OR:  last.__bool = l | r; break;
    case TOK_XOR:     last.__bool = l ^ r; break;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }
}

static void eval_floats(enum token_type op, float l, float r)
{
    last.dt = D_T_FLOAT;

    switch (op) {
    case TOK_EQ:      last.dt = D_T_INT; last.__int = l == r; break;
    case TOK_NEQ:     last.dt = D_T_INT; last.__int = l != r; break;
    case TOK_GT:      last.dt = D_T_INT; last.__int = l  > r; break;
    case TOK_LT:      last.dt = D_T_INT; last.__int = l  < r; break;
    case TOK_GE:      last.dt = D_T_INT; last.__int = l >= r; break;
    case TOK_LE:      last.dt = D_T_INT; last.__int = l <= r; break;
    case TOK_PLUS:    last.__float = l  + r; break;
    case TOK_MINUS:   last.__float = l  - r; break;
    case TOK_STAR:    last.__float = l  * r; break;
    case TOK_SLASH:   last.__float = l  / r; break;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }
}

static void eval_ints(
    enum token_type  op,
    int32_t          l,
    int32_t          r
) {
    last.dt = D_T_INT;

    switch (op) {
    case TOK_AND:     last.__int = l && r; break;
    case TOK_OR:      last.__int = l || r; break;
    case TOK_XOR:     last.__int = l  ^ r; break;
    case TOK_BIT_AND: last.__int = l  & r; break;
    case TOK_BIT_OR:  last.__int = l  | r; break;
    case TOK_EQ:      last.__int = l == r; break;
    case TOK_NEQ:     last.__int = l != r; break;
    case TOK_GT:      last.__int = l  > r; break;
    case TOK_LT:      last.__int = l  < r; break;
    case TOK_GE:      last.__int = l >= r; break;
    case TOK_LE:      last.__int = l <= r; break;
    case TOK_SHL:     last.__int = l << r; break;
    case TOK_SHR:     last.__int = l >> r; break;
    case TOK_PLUS:    last.__int = l  + r; break;
    case TOK_MINUS:   last.__int = l  - r; break;
    case TOK_STAR:    last.__int = l  * r; break;
    case TOK_SLASH:   last.__int = l  / r; break;
    case TOK_MOD:     last.__int = l  % r; break;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }
}

static void eval_chars(
    enum token_type  op,
    int32_t          l,
    int32_t          r
) {
    last.dt = D_T_CHAR;

    switch (op) {
    case TOK_AND:     last.dt = D_T_INT; last.__char = l && r; break;
    case TOK_OR:      last.dt = D_T_INT; last.__char = l || r; break;
    case TOK_XOR:     last.__char = l  ^ r; break;
    case TOK_BIT_AND: last.__char = l  & r; break;
    case TOK_BIT_OR:  last.__char = l  | r; break;
    case TOK_EQ:      last.dt = D_T_INT; last.__char = l == r; break;
    case TOK_NEQ:     last.dt = D_T_INT; last.__char = l != r; break;
    case TOK_GT:      last.dt = D_T_INT; last.__char = l  > r; break;
    case TOK_LT:      last.dt = D_T_INT; last.__char = l  < r; break;
    case TOK_GE:      last.dt = D_T_INT; last.__char = l >= r; break;
    case TOK_LE:      last.dt = D_T_INT; last.__char = l <= r; break;
    case TOK_SHL:     last.__char = l << r; break;
    case TOK_SHR:     last.__char = l >> r; break;
    case TOK_PLUS:    last.__char = l  + r; break;
    case TOK_MINUS:   last.__char = l  - r; break;
    case TOK_STAR:    last.__char = l  * r; break;
    case TOK_SLASH:   last.__char = l  / r; break;
    case TOK_MOD:     last.__char = l  % r; break;
    default:
        weak_unreachable("Unknown token type `%s`.", tok_to_string(op));
    }
}


static void compute(enum token_type op, struct value *l, struct value *r)
{
    if (l->dt != r->dt)
        weak_unreachable("dt(L) = %s, dt(R) = %s", data_type_to_string(l->dt), data_type_to_string(r->dt));

    switch (l->dt) {
    case D_T_BOOL:  eval_bools (op, l->__bool , r->__bool ); break;
    case D_T_CHAR:  eval_chars (op, l->__char , r->__char ); break;
    case D_T_INT:   eval_ints  (op, l->__int  , r->__int  ); break;
    case D_T_FLOAT: eval_floats(op, l->__float, r->__float); break;
    default:
        weak_unreachable("Unknown immediate type (numeric: %d).", l->dt);
    }
}

static void eval_bin(struct ir_bin *bin)
{
    instr_eval(bin->lhs);
    struct value l = last;

    instr_eval(bin->rhs);
    struct value r = last;

    compute(bin->op, &l, &r);
}



static void eval_store_imm(struct ir_store *store)
{
    assert(store->idx->type == IR_SYM && "TODO: Implement arrays");

    struct ir_imm *from    = store->body->ir;
    struct ir_sym *to      = store->idx->ir;
    struct type   *to_type = &to->type_info;

    switch (from->type) {
    case IMM_BOOL:  last.dt = D_T_BOOL;  last.__bool  = from->imm.__bool;  break;
    case IMM_CHAR:  last.dt = D_T_CHAR;  last.__char  = from->imm.__char;  break;
    case IMM_FLOAT: last.dt = D_T_FLOAT; last.__float = from->imm.__float; break;
    case IMM_INT:   last.dt = D_T_INT;   last.__int   = from->imm.__int;   break;
    default:
        weak_unreachable("Should not reach there");
    }

    set(to->idx, &last, to_type);
}

static void eval_store_sym(struct ir_store *store)
{
    /* Copy from one stack location to another. */
    assert(store->idx->type == IR_SYM && "TODO: Implement arrays");

    struct ir_sym *from      = store->body->ir;
    struct ir_sym *to        = store->idx ->ir;
    struct type   *from_type = &from->type_info;
    struct type   *  to_type = &to  ->type_info;

    struct value v = get(from->idx, from_type);
    set(to->idx, &v, to_type);
}

static void eval_store_bin(struct ir_store *store)
{
    instr_eval(store->body);
    assert(store->idx->type == IR_SYM && "TODO: Implement arrays");

    struct ir_sym *sym     = store->idx->ir;
    struct type   *to_type = &sym->type_info;

    set(sym->idx, &last, to_type);
}

static void eval_store_string(struct ir_store *store)
{
    struct ir_string *s = store->body->ir;
    assert(store->idx->type == IR_SYM && "TODO: Implement arrays");

    struct ir_sym *sym = store->idx->ir;

    set_string(sym->idx, s->imm);
}

static void eval_store_call(struct ir_store *store)
{
    instr_eval(store->body);
    assert(store->idx->type == IR_SYM && "TODO: Implement arrays");

    struct ir_sym *sym     =  store->idx->ir;
    struct type   *to_type = &sym->type_info;

    set(sym->idx, &last, to_type);
}

static void eval_store(struct ir_store *store)
{
    switch (store->body->type) {
    case IR_IMM:
        eval_store_imm(store);
        break;
    case IR_SYM:
        eval_store_sym(store);
        break;
    case IR_BIN:
        eval_store_bin(store);
        break;
    case IR_STRING:
        eval_store_string(store);
        break;
    case IR_FN_CALL:
        eval_store_call(store);
        break;
    default:
        break;
    }
}


static void eval_jmp(struct ir_node *jmp)
{
    instr_ptr = vector_at(jmp->cfg.succs, 0);
}

static void eval_cond(struct ir_node *__cond)
{
    struct ir_cond *cond = __cond->ir;
    instr_eval(cond->cond);

    /* Take biggest union value and compare
       with 0. No difference, which type. */
    bool should_jump = last.__int != 0;

    if (should_jump)
        instr_ptr = cond->target; /* True branch. */
    else
        instr_ptr = __cond->next; /* False branch. */
}

static void eval_ret(struct ir_ret *ret)
{
    if (ret->body)
        instr_eval(ret->body);

    instr_ptr = NULL;
}



static void instr_eval(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        eval_alloca(ir->ir);
        break;
    case IR_ALLOCA_ARRAY:
        eval_alloca_array(ir->ir);
        break;
    case IR_IMM:
        eval_imm(ir->ir);
        break;
    case IR_SYM:
        eval_sym(ir);
        break;
    case IR_JUMP:
        eval_jmp(ir);
        break;
    case IR_MEMBER:
    case IR_TYPE_DECL:
    case IR_FN_DECL:
        break;
    case IR_FN_CALL:
        call_eval(ir->ir);
        break;
    case IR_STORE:
        eval_store(ir->ir);
        break;
    case IR_BIN:
        eval_bin(ir->ir);
        break;
    case IR_RET:
        eval_ret(ir->ir);
        break;
    case IR_COND:
        eval_cond(ir);
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}



/* ==========================
   Call stack.
   ========================== */

/* Important notice about drawing stacks in LaTeX
   https://tex.stackexchange.com/questions/235000/drawing-an-activation-stack-in-latex */

static void printf_n(uint32_t count, char c)
{
    for (uint32_t i = 0; i < count; ++i) {
        putc(i % 2 != 0 ? c : '|', stdout);
    }
}

struct call_stack_entry {
    const char *name;
    uint64_t    sp;
};

typedef vector_t(struct call_stack_entry) call_stack_t;

static uint64_t call_depth;

/* TODO: Builtin function that prints stacktrace at
         the moment.

         strace();
         ` prints
         `
         call `main` (+0)
           call `fact` (+24)
             call `fact` (+144)
               call `fact` (+264)
                 call `fact` (+384)
                  call `fact` (+504)
*/
static void call_stack_head(const char *fname)
{
    printf_n(call_depth, ' ');
    printf("call `%s` (+%lu)\n", fname, sp);
    call_depth += 2;
}

static void call_stack_tail()
{
    call_depth -= 2;
}



/* ==========================
   Functions routines.
   ========================== */

static hashmap_t funs;

static void fun_list_init(struct ir_node *ir)
{
    while (ir) {
        struct ir_fn_decl *fun = ir->ir;
        hashmap_put(&funs, crc32_string(fun->name), (uint64_t) fun);
        ir = ir->next;
    }
}

static struct ir_fn_decl *fun_lookup(const char *name)
{
    uint64_t hash = crc32_string(name);

    bool ok = 0;
    uint64_t got = hashmap_get(&funs, hash, &ok);
    if (!ok)
        weak_unreachable("Function lookup failed for `%s`, CRC32: %lu", name, hash);

    return (struct ir_fn_decl *) got;
}

static void fun_eval(struct ir_fn_decl *decl)
{
    struct ir_node *it = decl->body;

    instr_ptr = it;

    while (instr_ptr) {
        struct ir_node *prev_ptr = instr_ptr;
        instr_eval(instr_ptr);

        /* Conditional and jump statements set up their
           successor instructions manually. Elsewise,
           we just peek the next one. */
        switch (prev_ptr->type) {
        case IR_COND:
        case IR_JUMP:
            break;
        default:
            if (instr_ptr)
                instr_ptr = vector_at(instr_ptr->cfg.succs, 0);
        }
    }
}



static void set_call_arg(struct ir_node *arg, uint64_t *sym)
{
    struct type *t = NULL;

    switch (arg->type) {
    case IR_SYM: t = &((struct ir_sym *) arg->ir)->type_info; break;
    case IR_IMM: t = &((struct ir_imm *) arg->ir)->type_info; break;
    /* TODO: Struct member access. */
    default:
        weak_unreachable(
            "Cannot pass `%s` as function argument",
            ir_type_to_string(arg->type)
        );
    }

    set((*sym)++, &last, t);
}

static void push_call_arg(struct ir_node *arg, uint64_t *sym)
{
    /* 1. Evaluate in current stack frame. */
    instr_eval(arg);
    /* 2. Push to the callee stack frame. */
    if (last.dt == D_T_STRING)
        push(*sym, strlen(last.__string));
    else
        push(*sym, dt_size(last.dt));
    /* 3. Set argument value in callee stack frame. */
    set_call_arg(arg, sym);
}

static void call_eval(struct ir_fn_call *fcall)
{
    /* Prologue @{ */
    uint64_t        sym            = 0;
    uint64_t        bp             = sp;
    struct ir_node *save_instr_ptr = instr_ptr;
    char            stack_map_copy[STACK_SIZE_BYTES];

    call_stack_head(fcall->name);
    memcpy(stack_map_copy, stack_map, STACK_SIZE_BYTES);

    struct ir_node *arg = fcall->args;
    while (arg) {
        push_call_arg(arg, &sym);
        arg = arg->next;
    }
    /* }@ */

    /* Body @{ */
    struct ir_fn_decl *fun = fun_lookup(fcall->name);
    fun_eval(fun);
    /* }@ */

    /* Epilogue @{ */
    sp = bp;
    instr_ptr = save_instr_ptr;
    memcpy(stack_map, stack_map_copy, STACK_SIZE_BYTES);
    call_stack_tail();
    /* }@ */
}



/* ==========================
   Driver code.
   ========================== */

int32_t eval(struct ir_unit *unit)
{
    reset();
    hashmap_reset(&funs, 512);

    fun_list_init(unit->fn_decls);

    struct ir_fn_call main = {
        .name = "main"
    };
    call_eval(&main);

    /* Required to be int. */
    if (last.dt != D_T_INT)
        weak_unreachable("main() return only ints.");

    return last.__int;
}