#include "middle_end/ir/type.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/meta.h"
#include <string.h>

#define MAX_IR_STMTS 10000

static struct type type_map[MAX_IR_STMTS];


static void init()
{
    memset(type_map, 0, sizeof (type_map));
}

static void type_pass(struct ir_node *ir);


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

static void type_pass_alloca(struct ir_alloca *alloca)
{
    uint64_t i     = alloca->idx;
    uint64_t bytes = alloca_size(alloca);

    type_map[i] = (struct type) {
        .dt         = alloca->dt,
        .ptr        = alloca->ptr_depth > 0,
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
        .ptr        = 0,
        .arity_size = alloca->arity_size,
        .bytes      = bytes
    };

    memcpy(type_map[i].arity, alloca->arity, alloca->arity_size);
}

static void type_pass_sym(struct ir_node *sym)
{
    struct ir_sym *s = sym->ir;
    struct type   *t = &type_map[s->idx];

    memcpy(&sym->meta.type, t, sizeof (*t));
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
    if (!r->is_void)
        type_pass(r->body);
}

static void type_pass_func_call(struct ir_func_call *call)
{
    struct ir_node *it = call->args;

    while (it) {
        type_pass(it);
        it = it->next;
    }
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
        type_pass_sym(ir);
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
    case IR_RET_VOID:
        type_pass_ret(ir->ir);
        break;
    case IR_FUNC_CALL:
        type_pass_func_call(ir->ir);
        break;
    case IR_MEMBER:
    case IR_TYPE_DECL:
    case IR_FUNC_DECL:
    case IR_IMM:
    case IR_STRING:
    case IR_JUMP:
    case IR_PHI:
        break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }
}

static void type_pass_fn(struct ir_func_decl *decl)
{
    init();
    struct ir_node *it = decl->body;

    while (it) {
        type_pass(it);
        it = it->next;
    }
}

void ir_type_pass(struct ir_unit *unit)
{
    struct ir_node *it = unit->func_decls;
    while (it) {
        type_pass_fn(it->ir);
        it = it->next;
    }
}