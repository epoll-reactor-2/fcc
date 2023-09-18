/* dump.c - IR stringify function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/dump.h"
#include "middle_end/ir/meta.h"
#include "front_end/lex/data_type.h"
#include "util/alloc.h"
#include "util/diagnostic.h"
#include "util/unreachable.h"
#include <assert.h>

const char *ir_type_to_string(enum ir_type t)
{
    switch (t) {
    case IR_ALLOCA:       return "IR_ALLOCA";
    case IR_ALLOCA_ARRAY: return "IR_ALLOCA_ARRAY";
    case IR_IMM:          return "IR_IMM";
    case IR_SYM:          return "IR_SYM";
    case IR_STORE:        return "IR_STORE";
    case IR_STORE_PTR:    return "IR_STORE_PTR";
    case IR_BIN:          return "IR_BIN";
    case IR_JUMP:         return "IR_JUMP";
    case IR_COND:         return "IR_COND";
    case IR_RET:          return "IR_RET";
    case IR_RET_VOID:     return "IR_RET_VOID";
    case IR_MEMBER:       return "IR_MEMBER";
    case IR_ARRAY_ACCESS: return "IR_ARRAY_ACCESS";
    case IR_TYPE_DECL:    return "IR_TYPE_DECL";
    case IR_FUNC_DECL:    return "IR_FUNC_DECL";
    case IR_FUNC_CALL:    return "IR_FUNC_CALL";
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", t);
    }
}

static void fprintf_n(FILE *mem, uint32_t count, char c)
{
    for (uint32_t i = 0; i < count; ++i)
        fputc(c, mem);
}

static void ir_dump_alloca(FILE *mem, struct ir_alloca *ir)
{
    fprintf(
        mem,
        "alloca %s%s %%%d",
        data_type_to_string(ir->dt),
        ir->ptr ? "*" : "",
        ir->idx
    );
}

static void ir_dump_alloca_array(FILE *mem, struct ir_alloca_array *ir)
{
    uint64_t total = ir->enclosure_lvls_size;

    fprintf(mem, "alloca ");
    for (uint64_t i = 0; i < total; ++i) {
        uint64_t e = ir->enclosure_lvls[i];
        fprintf(mem, "[%ld x ", e);
    }
    fprintf(mem, "%s", data_type_to_string(ir->dt));
    fprintf_n(mem, total, ']');
    fprintf(mem, " %%%d", ir->idx);
}

static void ir_dump_imm(FILE *mem, struct ir_imm *ir)
{
    switch (ir->type) {
    case IMM_BOOL:  fprintf(mem, "$%d", ir->imm.__bool); break;
    case IMM_CHAR:  fprintf(mem, "$%d", ir->imm.__char); break;
    case IMM_FLOAT: fprintf(mem, "$%f", ir->imm.__float); break;
    case IMM_INT:   fprintf(mem, "$%d", ir->imm.__int); break;
    default:
        weak_unreachable("Unknown immediate IR type (numeric: %d).", ir->type);
    }
}

static void ir_dump_sym(FILE *mem, struct ir_sym *ir)
{
    fprintf(mem, "%%%d", ir->idx);
}

static void ir_dump_store(FILE *mem, struct ir_store *ir)
{
    fprintf(mem, "store %%%d ", ir->idx);
    ir_dump_node(mem, ir->body);
}

static void ir_dump_store_ptr(FILE *mem, struct ir_store_ptr *ir)
{
    fprintf(mem, "store *%%%d ", ir->idx);
    ir_dump_node(mem, ir->body);
}

static void ir_dump_bin(FILE *mem, struct ir_bin *ir)
{
    const char *op = NULL;
    switch (ir->op) {
    case TOK_XOR:     op = "xor";     break;
    case TOK_BIT_AND: op = "bit_and"; break;
    case TOK_BIT_OR:  op = "bit_or";  break;
    case TOK_AND:     op = "and";     break;
    case TOK_OR:      op = "or";      break;
    case TOK_EQ:      op = "eq";      break;
    case TOK_NEQ:     op = "neq";     break;
    case TOK_GT:      op = "gt";      break;
    case TOK_LT:      op = "lt";      break;
    case TOK_GE:      op = "ge";      break;
    case TOK_LE:      op = "le";      break;
    case TOK_SHL:     op = "shl";     break;
    case TOK_SHR:     op = "shr";     break;
    case TOK_PLUS:    op = "add";     break;
    case TOK_MINUS:   op = "sub";     break;
    case TOK_STAR:    op = "mul";     break;
    case TOK_SLASH:   op = "div";     break;
    case TOK_MOD:     op = "mod";     break;
    /// \todo: %OP%_ASSIGN instructions...
    case TOK_ASSIGN:  op = "???";     break;
    default:
        weak_unreachable("Unknown operation: `%s`.", tok_to_string(ir->op));
    }

    ir_dump_node(mem, ir->lhs);
    fprintf(mem, " %s ", op);
    ir_dump_node(mem, ir->rhs);
}

static void ir_dump_jump(FILE *mem, struct ir_jump *ir)
{
    fprintf(mem, "jmp L%d", ir->idx);
}

static void ir_dump_cond(FILE *mem, struct ir_cond *ir)
{
    fprintf(mem, "if ");
    ir_dump_node(mem, ir->cond);
    fprintf(mem, " goto L%d", ir->goto_label);
}

static void ir_dump_ret(FILE *mem, struct ir_ret *ir)
{
    fprintf(mem, "ret ");
    ir_dump_node(mem, ir->body);
}

static void ir_dump_ret_void(FILE *mem)
{
    fprintf(mem, "ret");
}

static void ir_dump_member(FILE *mem, struct ir_member *ir)
{
    /// %1.0
    fprintf(mem, "%%%d.%d", ir->idx, ir->field_idx);
}

static void ir_dump_array_access(FILE *mem, struct ir_array_access *ir)
{
    fprintf(mem, "%%%d[", ir->idx);
    ir_dump_node(mem, ir->body);
    fprintf(mem, "]");
}

static void ir_dump_type_decl(FILE *mem, struct ir_type_decl *ir)
{
    fprintf(mem, "%%%s = {", ir->name);
    struct ir_node *it = ir->decls;
    while (it) {
        fprintf(mem, "\n    ");
        ir_dump_node(mem, it);
        it = it->next;
    }
    fprintf(mem, "\n}");
}

static void ir_dump_func_decl(FILE *mem, struct ir_func_decl *ir)
{
    fprintf(mem, "fun %s(", ir->name);
    struct ir_node *it = ir->args;
    while (it) {
        ir_dump_alloca(mem, it->ir);
        if (it->next != NULL)
            fprintf(mem, ", ");
        it = it->next;
    }
    fprintf(mem, "):");

    it = ir->body;
    while (it) {
        fprintf(mem, "\n% 8d:   ", it->instr_idx);
        ir_dump_node(mem, it);
        it = it->next;
    }
}

static void ir_dump_func_call(FILE *mem, struct ir_func_call *ir)
{
    fprintf(mem, "call %s(", ir->name);
    struct ir_node *it = ir->args;
    while (it) {
        ir_dump_node(mem, it);
        if (it->next != NULL)
            fprintf(mem, ", ");
        it = it->next;
    }
    fprintf(mem, ")");
}

void ir_dump_node(FILE *mem, struct ir_node *ir)
{
    switch (ir->type) {
    case IR_ALLOCA:       ir_dump_alloca(mem, ir->ir); break;
    case IR_ALLOCA_ARRAY: ir_dump_alloca_array(mem, ir->ir); break;
    case IR_IMM:          ir_dump_imm(mem, ir->ir); break;
    case IR_SYM:          ir_dump_sym(mem, ir->ir); break;
    case IR_STORE:        ir_dump_store(mem, ir->ir); break;
    case IR_STORE_PTR:    ir_dump_store_ptr(mem, ir->ir); break;
    case IR_BIN:          ir_dump_bin(mem, ir->ir); break;
    case IR_JUMP:         ir_dump_jump(mem, ir->ir); break;
    case IR_COND:         ir_dump_cond(mem, ir->ir); break;
    case IR_RET:          ir_dump_ret(mem, ir->ir); break;
    case IR_RET_VOID:     ir_dump_ret_void(mem); break;
    case IR_MEMBER:       ir_dump_member(mem, ir->ir); break;
    case IR_ARRAY_ACCESS: ir_dump_array_access(mem, ir->ir); break;
    case IR_TYPE_DECL:    ir_dump_type_decl(mem, ir->ir); break;
    case IR_FUNC_DECL:    ir_dump_func_decl(mem, ir->ir); break;
    case IR_FUNC_CALL:    ir_dump_func_call(mem, ir->ir); break;
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", ir->type);
    }

    if (ir->meta) {
        struct meta *meta = ir->meta;

        if (meta->sym_meta.loop)
            fprintf(mem, "(@loop)");

        if (meta->sym_meta.noalias)
            fprintf(mem, "(@noalias)");
    }
}

void ir_dump(FILE *mem, struct ir_func_decl *decl)
{
    ir_dump_func_decl(mem, decl);
    fprintf(mem, "\n");
}

static void ir_dump_node_dot(FILE *mem, struct ir_node *curr, struct ir_node *next)
{
    fprintf(mem, "    \"");
    ir_dump_node(mem, curr);
    fprintf(mem, "\" -> \"");
    ir_dump_node(mem, next);
    fprintf(mem, "\"\n");
}

__weak_really_inline static void ir_mark(bool *visited, struct ir_node *ir)
{
    visited[ir->instr_idx] = 1;
}

static void ir_dump_traverse(FILE *mem, bool *visited, struct ir_node *ir)
{
    if (visited[ir->instr_idx]) return;

    switch (ir->type) {
    case IR_IMM:
    case IR_SYM:
    case IR_BIN:
    case IR_MEMBER:
    case IR_ARRAY_ACCESS:
        break;
    case IR_STORE:
    case IR_ALLOCA:
    case IR_ALLOCA_ARRAY:
    case IR_FUNC_CALL:
    case IR_JUMP: {
        ir_mark(visited, ir);

        ir_dump_node_dot(mem, ir, ir->next);
        ir_dump_traverse(mem, visited, ir->next);
        break;
    }
    case IR_COND: {
        ir_mark(visited, ir);

        ir_dump_node_dot(mem, ir, ir->next);
        fprintf(mem, " [ label = \"  true\"]\n");

        ir_dump_node_dot(mem, ir, ir->next_else);
        fprintf(mem, " [ label = \"  false\"]\n");

        ir_dump_traverse(mem, visited, ir->next);
        ir_dump_traverse(mem, visited, ir->next_else);
        break;
    }
    case IR_RET:
    case IR_RET_VOID: {
        ir_mark(visited, ir);

        if (ir->next) {
            ir_dump_node_dot(mem, ir, ir->next);
            ir_dump_traverse(mem, visited, ir->next);
        }
        break;
    }
    default:
        break;
    }
}

void ir_dump_graph_dot(FILE *mem, struct ir_func_decl *decl)
{
    fprintf(
        mem,
        "digraph {\n"
        "    node [shape=box];\n"
    );

    bool visited[8192] = {0};

    ir_dump_traverse(mem, visited, decl->body);

    fprintf(mem, "}\n");
}

void ir_dump_dom_tree(FILE *mem, struct ir_func_decl *decl)
{
    fprintf(
        mem,
        "digraph {\n"
        "    node [shape=box];\n"
    );

    struct ir_node *it = decl->body;
    while (it) {
        if (it->idom != NULL)
            ir_dump_node_dot(mem, it->idom, it);
        it = it->next;
    }

    fprintf(mem, "}\n");
}