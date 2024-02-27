/* type.c - IR pass that adds type information.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/type.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/meta.h"
#include "util/crc32.h"
#include "util/hashmap.h"
#include <string.h>

#define MAX_IR_STMTS 10000

static struct type type_map[MAX_IR_STMTS];
static hashmap_t   fn_map;



uint64_t ir_type_size(enum data_type dt)
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

static enum data_type imm_type_to_dt(enum ir_imm_type t)
{
    switch (t) {
    case IMM_BOOL:  return D_T_BOOL;
    case IMM_CHAR:  return D_T_CHAR;
    case IMM_INT:   return D_T_INT;
    case IMM_FLOAT: return D_T_FLOAT;
    default:
        weak_unreachable("Unknown data type (numeric: %d)", t);
    }
}



static void fn_type_save(struct ir_fn_decl *decl)
{
    struct type *t = weak_calloc(1, sizeof (struct type));

    t->dt = decl->ret_type;
    t->ptr_depth = decl->ptr_depth;
    t->bytes = t->ptr_depth > 0 ? 8 : ir_type_size(t->dt);

    hashmap_put(&fn_map, crc32_string(decl->name), (uint64_t) t);
}

struct type *fn_type_lookup(const char *name)
{
    bool     ok   = 0;
    uint64_t hash = crc32_string(name);
    uint64_t addr = hashmap_get(&fn_map, hash, &ok);

    if (!ok)
        weak_unreachable("Function `%s` not found", name);

    return (struct type *) addr;
}

static void init_fn_state()
{
    memset(type_map, 0, sizeof (type_map));
}

static void init_fn_map()
{
    hashmap_reset(&fn_map, 16);
}

static void reset_fn_map()
{
    hashmap_foreach(&fn_map, k, v) {
        (void) k;
        weak_free((void *) v);
    }
    hashmap_destroy(&fn_map);
}

static void type_pass(struct ir_node *ir);



static uint64_t alloca_size(struct ir_alloca *alloca)
{
    if (alloca->ptr_depth > 0)
        return 8;

    return ir_type_size(alloca->dt);
}

static uint64_t alloca_array_size(struct ir_alloca_array *alloca)
{
    uint64_t siz = 1;

    for (uint64_t i = 0; i < alloca->arity_size; ++i)
        siz *= alloca->arity[i];
    siz *= ir_type_size(alloca->dt);

    return siz;
}

static void type_pass_alloca(struct ir_alloca *alloca)
{
    uint64_t i     = alloca->idx;
    uint64_t bytes = alloca_size(alloca);

    type_map[i] = (struct type) {
        .dt         = alloca->dt,
        .ptr_depth  = alloca->ptr_depth,
        .arity_size = 0,
        .bytes      = bytes
    };

    memset(type_map[i].arity, 0, sizeof (type_map[i].arity));
}

static void type_pass_alloca_array(struct ir_alloca_array *alloca)
{
    uint64_t i     = alloca->idx;
    uint64_t bytes = alloca_array_size(alloca);

    type_map[i] = (struct type) {
        .dt         = alloca->dt,
        .ptr_depth  = 0,
        .arity_size = alloca->arity_size,
        .bytes      = bytes
    };

    memcpy(type_map[i].arity, alloca->arity, alloca->arity_size);
}

static void type_pass_imm(struct ir_imm *i)
{
    enum data_type dt = imm_type_to_dt(i->type);

    i->type_info = (struct type) {
        .dt         = dt,
        .ptr_depth  = 0,
        .arity_size = 0,
        .bytes      = ir_type_size(dt)
    };

    memset(&i->type_info.arity, 0, sizeof (i->type_info.arity));
}

static void type_pass_fn_call(struct ir_fn_call *call)
{
    struct ir_node *it = call->args;

    while (it) {
        type_pass(it);
        it = it->next;
    }

    struct type *t = fn_type_lookup(call->name);
    memcpy(&call->type_info, t, sizeof (*t));
}

static void type_pass_sym(struct ir_sym *s)
{
    struct type *t = &type_map[s->idx];

    memcpy(&s->type_info, t, sizeof (*t));
}

static void type_pass_store(struct ir_store *s)
{
    type_pass(s->idx);
    type_pass(s->body);
}

static void type_pass_bin(struct ir_bin *b)
{
    type_pass(b->lhs);
    type_pass(b->rhs);
}

static void type_pass_cond(struct ir_cond *c)
{
    type_pass(c->cond);
}

static void type_pass_ret(struct ir_ret *r)
{
    if (r->body)
        type_pass(r->body);
}

static void type_pass(struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:
        type_pass_alloca(ir->ir);
        break;
    case IR_ALLOCA_ARRAY:
        type_pass_alloca_array(ir->ir);
        break;
    case IR_SYM:
        type_pass_sym(ir->ir);
        break;
    case IR_IMM:
        type_pass_imm(ir->ir);
        break;
    case IR_STORE:
        type_pass_store(ir->ir);
        break;
    case IR_BIN:
        type_pass_bin(ir->ir);
        break;
    case IR_COND:
        type_pass_cond(ir->ir);
        break;
    case IR_RET:
        type_pass_ret(ir->ir);
        break;
    case IR_FN_CALL:
        type_pass_fn_call(ir->ir);
        break;
    case IR_MEMBER:
    case IR_TYPE_DECL:
    case IR_FN_DECL:
    case IR_STRING:
    case IR_JUMP:
    case IR_PHI:
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}

static void type_pass_fn(struct ir_fn_decl *decl)
{
    init_fn_state();
    struct ir_node *it = decl->args;
    while (it) {
        type_pass(it);
        it = it->next;
    }

    it = decl->body;
    while (it) {
        type_pass(it);
        it = it->next;
    }
}

void ir_type_pass(struct ir_unit *unit)
{
    init_fn_map();

    struct ir_node *it = unit->fn_decls;
    while (it) {
        fn_type_save(it->ir);
        it = it->next;
    }

    it = unit->fn_decls;
    while (it) {
        type_pass_fn(it->ir);
        it = it->next;
    }

    reset_fn_map();
}