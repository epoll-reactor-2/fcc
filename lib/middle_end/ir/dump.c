/* dump.c - IR stringify function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/dump.h"
#include "front_end/lex/data_type.h"
#include "middle_end/ir/meta.h"
#include "util/unreachable.h"

const char *ir_type_to_string(enum ir_type t)
{
    switch (t) {
    case IR_ALLOCA:       return "IR_ALLOCA";
    case IR_ALLOCA_ARRAY: return "IR_ALLOCA_ARRAY";
    case IR_IMM:          return "IR_IMM";
    case IR_SYM:          return "IR_SYM";
    case IR_STORE:        return "IR_STORE";
    case IR_BIN:          return "IR_BIN";
    case IR_JUMP:         return "IR_JUMP";
    case IR_COND:         return "IR_COND";
    case IR_RET:          return "IR_RET";
    case IR_RET_VOID:     return "IR_RET_VOID";
    case IR_MEMBER:       return "IR_MEMBER";
    case IR_TYPE_DECL:    return "IR_TYPE_DECL";
    case IR_FUNC_DECL:    return "IR_FUNC_DECL";
    case IR_FUNC_CALL:    return "IR_FUNC_CALL";
    default:
        weak_unreachable("Unknown IR type (numeric: %d).", t);
    }
}

static void ir_dump_alloca(FILE *mem, struct ir_alloca *ir)
{
    fprintf(
        mem,
        "%s %st%d",
        data_type_to_string(ir->dt),
        ir->indir_lvl ? "* " : "",
        ir->idx
    );
}

static void ir_dump_alloca_array(FILE *mem, struct ir_alloca_array *ir)
{
    uint64_t total = ir->enclosure_lvls_size;

    fprintf(mem, "%s t%d[", data_type_to_string(ir->dt), ir->idx);
    for (uint64_t i = 0; i < total; ++i) {
        uint64_t e = ir->enclosure_lvls[i];
        fprintf(mem, "%ld", e);
        if (i < total - 1) {
            fprintf(mem, " x ");
        }
    }
    fprintf(mem, "]");
}

static void ir_dump_imm(FILE *mem, struct ir_imm *ir)
{
    switch (ir->type) {
    case IMM_BOOL:  fprintf(mem, "%d", ir->imm.__bool); break;
    case IMM_CHAR:  fprintf(mem, "'%c'", ir->imm.__char); break;
    case IMM_FLOAT: fprintf(mem, "%f", ir->imm.__float); break;
    case IMM_INT:   fprintf(mem, "%d", ir->imm.__int); break;
    default:
        weak_unreachable("Unknown immediate IR type (numeric: %d).", ir->type);
    }
}

static void ir_dump_string(FILE *mem, struct ir_string *ir)
{
    fprintf(mem, "\"%s\"", ir->imm);
}

static void ir_dump_sym(FILE *mem, struct ir_sym *ir)
{
    fprintf(mem, "%st%d", ir->deref ? "*" : "", ir->idx);
}

static void ir_dump_store(FILE *mem, struct ir_store *ir)
{
    ir_dump_node(mem, ir->idx);
    fprintf(mem, " = ");
    ir_dump_node(mem, ir->body);
}

static void ir_dump_bin(FILE *mem, struct ir_bin *ir)
{
    const char *op = tok_to_string(ir->op);

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
    case IR_STRING:       ir_dump_string(mem, ir->ir); break;
    case IR_SYM:          ir_dump_sym(mem, ir->ir); break;
    case IR_STORE:        ir_dump_store(mem, ir->ir); break;
    case IR_BIN:          ir_dump_bin(mem, ir->ir); break;
    case IR_JUMP:         ir_dump_jump(mem, ir->ir); break;
    case IR_COND:         ir_dump_cond(mem, ir->ir); break;
    case IR_RET:          ir_dump_ret(mem, ir->ir); break;
    case IR_RET_VOID:     ir_dump_ret_void(mem); break;
    case IR_MEMBER:       ir_dump_member(mem, ir->ir); break;
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

void ir_dump_unit(FILE *mem, struct ir_unit *unit)
{
    struct ir_node *it = unit->func_decls;
    while (it) {
        ir_dump(mem, it->ir);
        it = it->next;
    }
}

static void ir_dump_node_dot(FILE *mem, struct ir_node *curr, struct ir_node *next)
{
    fprintf(mem, "    \"%d:   ", curr->instr_idx);
    ir_dump_node(mem, curr);
    fprintf(mem, "\" -> \"%d:   ", next->instr_idx);
    ir_dump_node(mem, next);
    fprintf(mem, "\"\n");
}

static void ir_dump_node_ddg(FILE *mem, struct ir_node *ir)
{
    vector_foreach(ir->ddg_stmts, i) {
        struct ir_node *dependence = vector_at(ir->ddg_stmts, i);
        fprintf(mem, "    \"%d:   ", ir->instr_idx);
        ir_dump_node(mem, ir);
        fprintf(mem, "\" -> \"%d:   ", dependence->instr_idx);
        ir_dump_node(mem, dependence);
        fprintf(mem, "\" [style = dotted]\n");
    }
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

static void ir_dump_cfg_traverse(FILE *mem, struct ir_node *ir)
{
    struct ir_node *it = ir;
    uint64_t cfg_no = 0;
    uint64_t cluster_no = 0;

    fprintf(mem, "    start -> \"%d:   ", it->instr_idx);
    ir_dump_node(mem, it);
    fprintf(mem, "\"\n");

    while (it) {
        bool should_split = 0;
        bool first = it == ir;
        should_split |= first;
        should_split |= cfg_no != it->cfg_block_no;
        should_split |= it->next && it->next->prev_else != NULL;

        if (should_split) {
            if (!first)
                fprintf(mem, "} ");

            fprintf(mem, "subgraph cluster%ld {\n", cluster_no++);
        }

        switch (it->type) {
        case IR_JUMP: {
            struct ir_jump *jump = it->ir;
            ir_dump_node_dot(mem, it, jump->target);
            break;
        }
        case IR_COND: {
            struct ir_cond *cond = it->ir;
            ir_dump_node_dot(mem, it, it->next_else);
            fprintf(mem, " [ label = \"  false\"]\n");

            fprintf(mem, "} subgraph cluster%ld {\n", cluster_no++);

            ir_dump_node_dot(mem, it, cond->target);
            fprintf(mem, " [ label = \"  true\"]\n");

            /// This is reorder trick for dot language.
            /// Even though dot specification says, that
            /// in general order of subgraphs and nodes
            /// must not affect output PNG, this always
            /// happens. Thanks to this subgraph reindexing,
            /// condition targets both on true and false
            /// branches are located in the same subgraph.
            --cluster_no;
            --cluster_no;
            break;
        }
        case IR_RET:
        case IR_RET_VOID: {
            fprintf(mem, "    \"%d:   ", it->instr_idx);
            ir_dump_node(mem, it);
            fprintf(mem, "\" -> exit\n");
            break;
        }
        default: {
            if (it->next)
                ir_dump_node_dot(mem, it, it->next);
            break;
        }
        }

        ir_dump_node_ddg(mem, it);

        cfg_no = it->cfg_block_no;
        it = it->next;
    }

    fprintf(
        mem,
        "}\n"
        "    start [shape=Mdiamond]\n"
        "    exit  [shape=Mdiamond]\n"
    );
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

void ir_dump_cfg(FILE *mem, struct ir_func_decl *decl)
{
    fprintf(
        mem,
        "digraph {\n"
        "    compound=true;\n"
        "    node [shape=box,color=black];\n"
        "    graph [shape=box,style=filled,color=lightgrey];\n"
    );

    ir_dump_cfg_traverse(mem, decl->body);

    /// Wierd specific of algorithm above forces
    /// us to paste extra `}`, but this makes code much
    /// simpler.
    fprintf(mem, "}\n");
}

void ir_dump_dom_tree(FILE *mem, struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;
    uint64_t cfg_no = 0;
    uint64_t cluster_no = 0;

    fprintf(
        mem,
        "digraph {\n"
        "    compound=true;\n"
        "    node [shape=box,color=black];\n"
        "    graph [shape=box,style=filled,color=lightgrey];\n"
    );

    while (it) {
        bool should_split = 0;
        bool first = it == decl->body;
        should_split |= first;
        should_split |= cfg_no != it->cfg_block_no;
        should_split |= it->next && it->next->prev_else != NULL;

        if (should_split) {
            if (!first)
                fprintf(mem, "} ");

            fprintf(mem, "subgraph cluster%ld {\n", cluster_no++);
        }

        if (it->idom)
            ir_dump_node_dot(mem, it->idom, it);

        cfg_no = it->cfg_block_no;
        it = it->next;
    }

    fprintf(
        mem,
        "}\n"
    );

    fprintf(mem, "}\n");
}