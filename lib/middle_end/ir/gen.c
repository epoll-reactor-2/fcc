/* gen.c - IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/gen.h"
#include "middle_end/ir/meta.h"
#include "middle_end/ir/graph.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/storage.h"
#include "middle_end/ir/ir.h"
#include "front_end/ast/ast.h"
#include "util/crc32.h"
#include "util/vector.h"
#include "util/unreachable.h"
#include "util/hashmap.h"
#include <assert.h>
#include <string.h>

typedef vector_t(struct ir_node *) ir_array_t;

/// Total list of functions.
static ir_array_t      ir_func_decls;
static struct ir_node *ir_first;
static struct ir_node *ir_last;
static struct ir_node *ir_prev;
/// Used to count alloca instructions.
/// Conditions:
/// - reset at the start of each function declaration,
/// - increments with every created alloca instruction.
static int32_t         ir_var_idx;

static bool            ir_save_first;

static bool            ir_meta_is_loop;

static int32_t         ir_meta_loop_idx;

static hashmap_t       ir_func_return_types;

static void ir_func_add_return_type(const char *name, enum data_type dt)
{
    hashmap_put(&ir_func_return_types, crc32_string(name), (uint64_t) dt);
}

static enum data_type ir_func_return_type(const char *name)
{
    bool ok = 0;
    uint64_t name_hash = crc32_string(name);
    uint64_t got = hashmap_get(&ir_func_return_types, name_hash, &ok);
    if (!ok)
        weak_unreachable("Cannot get return type for function `%s`", name);

    return (enum data_type) got;
}

static void ir_try_add_meta(struct ir_node *ir)
{
    if (!ir_meta_is_loop) return;

    struct meta *meta = meta_init(IR_META_VAR);

    if (ir_meta_is_loop) {
        meta->sym_meta.loop = 1;
        meta->sym_meta.loop_idx = ir_meta_loop_idx++;
    }

    ir->meta = meta;
}

static void ir_insert(struct ir_node *new_node)
{
    __weak_debug({
        __weak_debug_msg("Insert IR (instr_idx: %d) :", new_node->instr_idx);
        ir_dump_node(stdout, new_node);
        puts("");
    });

    if (ir_save_first) {
        ir_first = new_node;
        ir_save_first = 0;
    }
    ir_last = new_node;

    if (ir_prev == NULL) {
        ir_prev = new_node;
        new_node->prev = NULL;  // Set prev to NULL for the first node
        new_node->prev_else = NULL;
        return;
    }

    ir_prev->next = new_node;
    new_node->prev = ir_prev;
    new_node->prev_else = NULL;
    ir_prev = new_node;

    ir_try_add_meta(new_node);
}

static void invalidate()
{
    vector_free(ir_func_decls);
    ir_var_idx = 0;
    ir_first = NULL;
    ir_last = NULL;
    ir_prev = NULL;

    if (ir_func_return_types.buckets) {
        hashmap_destroy(&ir_func_return_types);
    }
    hashmap_init(&ir_func_return_types, 32);
}

static void visit_ast(struct ast_node *ast);

/// Primitives. Are not pushed to ir_stmts, because
/// they are immediate values.
static void visit_ast_bool(struct ast_bool *ast)
{
    ir_last = ir_imm_bool_init(ast->value);
}

static void visit_ast_char(struct ast_char *ast)
{
    ir_last = ir_imm_char_init(ast->value);
}

static void visit_ast_float(struct ast_float *ast)
{
    ir_last = ir_imm_float_init(ast->value);
}

static void visit_ast_num(struct ast_num *ast)
{
    ir_last = ir_imm_int_init(ast->value);
}

static void visit_ast_string(struct ast_string *ast) { (void) ast; }

static void emit_assign(struct ast_binary *ast, struct ir_node **last_assign)
{
    visit_ast(ast->lhs);
    struct ir_node *lhs = ir_last;

    struct ir_sym *l_sym = lhs->ir;
    *last_assign = ir_last;

    __weak_debug_msg("-- IR meta save index %%%d\n", l_sym->idx);
    fflush(stdout);

    visit_ast(ast->rhs);
    struct ir_node *rhs = ir_last;

    struct ir_node *store = NULL;

    switch (rhs->type) {
    case IR_IMM: {
        store = ir_store_imm_init(l_sym->idx, rhs);
        break;
    }
    case IR_SYM: {
        struct ir_sym *r_sym  = rhs->ir;
        store = ir_store_sym_init(l_sym->idx, r_sym->idx);
        break;
    }
    default:
        weak_unreachable("Unexpected store type (numeric: %d).", rhs->type);
    }

    ir_insert(store);
}

static void emit_bin(struct ast_binary *ast, struct ir_node *last_assign)
{
    struct ir_node *alloca = ir_alloca_init(D_T_INT, ir_var_idx++);
    int32_t         alloca_idx = ((struct ir_alloca *) alloca->ir)->idx;

    ir_insert(alloca);

    visit_ast(ast->lhs);
    struct ir_node *lhs = ir_last;
    visit_ast(ast->rhs);
    struct ir_node *rhs = ir_last;

    struct ir_node *bin = ir_bin_init(ast->operation, lhs, rhs);
    ir_last = ir_store_bin_init(alloca_idx, bin);

    if (last_assign != NULL) {
        struct ir_sym  *assign = last_assign->ir;

        if (lhs->type == IR_SYM) {
            struct ir_sym *sym = lhs->ir;

            if (sym->idx == assign->idx) {
                struct meta *meta = meta_init(IR_META_VAR);
                meta->sym_meta.noalias = 1;
                lhs->meta = meta;
            }
        }

        if (rhs->type == IR_SYM) {
            struct ir_sym *sym = rhs->ir;

            if (sym->idx == assign->idx) {
                struct meta *meta = meta_init(IR_META_VAR);
                meta->sym_meta.noalias = 1;
                rhs->meta = meta;
            }
        }
    }

    ir_insert(ir_last);
    ir_last = ir_sym_init(alloca_idx);
}

static void visit_ast_binary(struct ast_binary *ast)
{
    /// Symbol.
    static struct ir_node *last_assign = NULL;
    static int32_t depth = 0;

    if (ast->operation == TOK_ASSIGN) {
        ++depth;
        emit_assign(ast, &last_assign);
        --depth;
    } else {
        ++depth;
        emit_bin(ast, last_assign);
        --depth;
    }

    if (depth == 0) {
        /// Depth is 0 means end of the binary expression
        /// at the program syntax level.
        ///
        /// int a = /// Depth is 0.
        ///       b + c /// Depth is 1, then 2.
        ///         d + e; /// Depth is 3, then 4.
        /// /// Depth is again 0.
        last_assign = NULL;
    }
}

static void visit_ast_break(struct ast_break *ast) { (void) ast; }
static void visit_ast_continue(struct ast_continue *ast) { (void) ast; }

static void visit_ast_for(struct ast_for *ast)
{
    /// Schema:
    ///
    /// L0:  init variable
    /// L1:  if condition is true jump to L3
    /// L2:  jump to L7 (exit label)
    /// L3:  body instr 1
    /// L4:  body instr 2
    /// L5:  increment
    /// L6:  jump to L1 (condition)
    /// L7:  after for instr

    /// Initial part is optional.
    ir_meta_is_loop = 1;
    if (ast->init) visit_ast(ast->init);
    ir_meta_is_loop = 0;

    /// Body starts with condition that is checked on each
    /// iteration.
    int32_t         next_iter_jump_idx = 0;
    struct ir_node *cond               = NULL;
    struct ir_node *exit_jmp           = NULL;
    struct ir_jump *exit_jmp_ptr       = NULL;

    /// Condition is optional.
    if (ast->condition) {
        next_iter_jump_idx       = ir_last->instr_idx + 1;
        visit_ast(ast->condition);
        struct ir_node *cond_bin = ir_bin_init(TOK_NEQ, ir_last, ir_imm_int_init(0));
        cond                     = ir_cond_init(cond_bin, /*Not used for now.*/-1);
        exit_jmp                 = ir_jump_init(/*Not used for now.*/-1);
        exit_jmp_ptr             = exit_jmp->ir;
        struct ir_cond *cond_ptr = cond->ir;

        ir_insert(cond);
        ir_insert(exit_jmp);

        cond_ptr->goto_label = ir_last->instr_idx + 1;
    } else {
        next_iter_jump_idx = ir_last->instr_idx + 1;
    }

    visit_ast(ast->body);
    /// Increment is optional.

    ir_meta_is_loop = 1;
    if (ast->increment) visit_ast(ast->increment);
    ir_meta_is_loop = 0;

    ir_last = ir_jump_init(next_iter_jump_idx);

    if (ast->condition) {
        cond->next_else = exit_jmp;
        exit_jmp->prev = cond;
        exit_jmp_ptr->idx = ir_last->instr_idx + 1;
    }

    ir_insert(ir_last);
}

static void visit_ast_while(struct ast_while *ast)
{
    /// Schema:
    ///
    /// L0: if condition is true jump to L2
    /// L1: jump to L5 (exit label)
    /// L2: body instr 1
    /// L3: body instr 2
    /// L4: jump to L0 (condition)
    /// L5: after while instr

    int32_t         next_iter_idx = ir_last->instr_idx + 1;

    ir_meta_is_loop = 1;
    visit_ast(ast->condition);
    ir_meta_is_loop = 0;

    struct ir_node *cond_bin      = ir_bin_init(TOK_NEQ, ir_last, ir_imm_int_init(0));
    struct ir_node *cond          = ir_cond_init(cond_bin, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr      = cond->ir;
    struct ir_node *exit_jmp      = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *exit_jmp_ptr  = exit_jmp->ir;

    ir_insert(cond);
    ir_insert(exit_jmp);

    cond_ptr->goto_label = exit_jmp->instr_idx + 1;

    visit_ast(ast->body);

    struct ir_node *next_iter_jmp = ir_jump_init(next_iter_idx);
    ir_insert(next_iter_jmp);

    cond->next_else = exit_jmp;
    exit_jmp->prev = cond;

    exit_jmp_ptr->idx = next_iter_jmp->instr_idx + 1;
}

static void visit_ast_do_while(struct ast_do_while *ast)
{
    /// Schema:
    ///
    /// L0: body instr 1
    /// L1: body instr 2
    /// L2: allocate temporary for condition
    /// L3: store condition in temporary
    /// L4: if condition is true jump to L0

    int32_t stmt_begin;

    if (ir_last == NULL)
        stmt_begin = 0;
    else
        stmt_begin = ir_last->instr_idx;

    visit_ast(ast->body);

    ir_meta_is_loop = 1;
    visit_ast(ast->condition);
    ir_meta_is_loop = 0;

    struct ir_node *cond_bin = ir_bin_init(TOK_NEQ, ir_last, ir_imm_int_init(0));
    struct ir_node *cond     = ir_cond_init(cond_bin, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr = cond->ir;

    ir_insert(cond);

    /// \todo: next_else pointer should lead to statement
    ///        out of do-while (next one after it).

    cond_ptr->goto_label = stmt_begin + 1;
}

static void visit_ast_if(struct ast_if *ast)
{
    /// Schema:
    ///
    ///      if condition is true jump to L1
    /// L0:  jump to L3 (exit label)
    /// L1:  body instr 1 (first if stmt)
    /// L2:  body instr 2
    /// L3:  after if
    ///
    /// or
    ///      if condition is true jump to L1
    /// L0:  jump to L4 (else label)
    /// L1:  body instr 1 (first if stmt)
    /// L2:  body instr 2
    /// L3:  jump to L6
    /// L4:  else body instr 1
    /// L5:  else body instr 2
    /// L6:  after if
    visit_ast(ast->condition);
    assert((
        ir_last->type == IR_IMM ||
        ir_last->type == IR_SYM
    ) && ("Immediate value or symbol required."));
    /// Condition always looks like comparison with 0.
    ///
    /// Possible cases:
    ///                    v Binary operation result.
    /// - if (1 + 1) -> if sym neq $0 goto ...
    /// - if (1    ) -> if imm neq $0 goto ...
    /// - if (var  ) -> if sym neq $0 goto ...
    ir_last = ir_bin_init(TOK_NEQ, ir_last, ir_imm_int_init(0));

    struct ir_node *cond        = ir_cond_init(ir_last, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr    = cond->ir;
    struct ir_node *end_jmp     = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *end_jmp_ptr = end_jmp->ir;

    /// Body starts after exit jump.
    cond_ptr->goto_label = end_jmp->instr_idx + 1;
    ir_insert(cond);
    ir_insert(end_jmp);

    visit_ast(ast->body);
    /// Even with code like
    /// void f() { if (x) { f(); } }
    /// this will make us to jump to the `ret`
    /// instruction, which terminates each (regardless
    /// on the return type) function.
    end_jmp_ptr->idx = ir_last->instr_idx + 1;

    cond->next_else = end_jmp;
    end_jmp->prev = cond;

    if (!ast->else_body) return;
    struct ir_node *else_jmp = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *else_jmp_ptr = else_jmp->ir;
    /// Index of this jump will be changed through pointer.
    ir_insert(else_jmp);

    /// Jump over the `then` statement to `else`.
    end_jmp_ptr->idx = ir_last->instr_idx
        // + 1  /// Jump statement.
        + 1; /// The next one (first in `else` part).
    visit_ast(ast->else_body);
    /// `then` part ends with jump over `else` part.
    else_jmp_ptr->idx = ir_last->instr_idx + 1;
}

static void visit_ast_return(struct ast_return *ast)
{
    memset(&ir_last, 0, sizeof (ir_last));
    if (ast->operand) {
        visit_ast(ast->operand);
    }
    ir_last = ir_ret_init(
        /*is_void=*/!ast->operand,
        /*op=*/ir_last
    );
    ir_insert(ir_last);
}

static void visit_ast_symbol(struct ast_symbol *ast)
{
    int32_t idx = ir_storage_get(ast->value);
    ir_last = ir_sym_init(idx);
}

/// Note: unary statements always have @noalias attribute.
static void visit_ast_unary(struct ast_unary *ast)
{
    visit_ast(ast->operand);
    assert((
        ir_last->type == IR_SYM
    ) && ("Unary operator expects variable argument."));
    struct ir_sym *sym = ir_last->ir;
    struct ir_node *sym_node = ir_last;

    switch (ast->operation) {
    case TOK_INC:
        ir_last = ir_bin_init(TOK_PLUS,  ir_last, ir_imm_int_init(1));
        break;
    case TOK_DEC:
        ir_last = ir_bin_init(TOK_MINUS, ir_last, ir_imm_int_init(1));
        break;
    default:
        weak_unreachable("Unknown unary operator (numeric: %d).", ast->operation);
    }
    ir_last = ir_store_bin_init(sym->idx, ir_last);

    struct meta *meta = meta_init(IR_META_VAR);
    meta->sym_meta.noalias = 1;
    sym_node->meta = meta;

    ir_insert(ir_last);
}

static void visit_ast_struct_decl(struct ast_struct_decl *ast) { (void) ast; }

static void visit_ast_var_decl(struct ast_var_decl *ast)
{
    int32_t next_idx = ir_var_idx++;
    ir_last = ir_alloca_init(ast->dt, next_idx);
    /// Used as function argument or as function body statement.
    ir_insert(ir_last);
    ir_storage_push(ast->name, next_idx);

    if (ast->body) {
        visit_ast(ast->body);

        switch (ir_last->type) {
        case IR_IMM: {
            ir_last = ir_store_imm_init(next_idx, ir_last);
            break;
        }
        case IR_SYM: {
            struct ir_sym *sym = ir_last->ir;
            ir_last = ir_store_sym_init(next_idx, sym->idx);
            break;
        }
        default:
            weak_unreachable(
                "Expected symbol or immediate value as variable initializer, "
                "got (numeric: %d).", ir_last->type
            );
        }
        ir_insert(ir_last);
    }
}

static void visit_ast_array_decl(struct ast_array_decl *ast) { (void) ast; }
static void visit_ast_array_access(struct ast_array_access *ast) { (void) ast; }
static void visit_ast_member(struct ast_member *ast) { (void) ast; }

static void visit_ast_compound(struct ast_compound *ast)
{
    for (uint64_t i = 0; i < ast->size; ++i)
        visit_ast(ast->stmts[i]);
}

static void visit_ast_function_decl(struct ast_function_decl *decl)
{
    ir_storage_init();

    ir_var_idx = 0;
    ir_first = NULL;
    ir_last = NULL;
    ir_prev = NULL;
    ir_save_first = 1;

    visit_ast(decl->args);
    struct ir_node *args = ir_first;

    ir_first = NULL;
    ir_last = NULL;
    ir_prev = NULL;
    ir_save_first = 1;

    ir_reset_internal_state();

    visit_ast(decl->body);
    if (decl->data_type == D_T_VOID) {
        struct ir_node *ret_body = ir_node_init(IR_RET_VOID, NULL);
        ir_insert(ir_ret_init(true, ret_body));
    }
    struct ir_node *body = ir_first;

    vector_push_back(
        ir_func_decls,
        ir_func_decl_init(
            decl->data_type,
            decl->name,
            args,
            body
        )
    );

    ir_func_add_return_type(decl->name, decl->data_type);

    ir_storage_reset();
}

static void visit_ast_function_call(struct ast_function_call *ast)
{
    /// Save and restore IR-related data to use
    /// ir_insert().
    struct ir_node *saved_ir_first = ir_first;
    struct ir_node *saved_ir_last = ir_last;
    struct ir_node *saved_ir_prev = ir_prev;
    bool            saved_ir_save_first = ir_save_first;

    ir_first = NULL;
    ir_last = NULL;
    ir_prev = NULL;
    ir_save_first = 1;

    struct ast_compound *args_ast = ast->args->ast;
    for (uint64_t i = 0; i < args_ast->size; ++i) {
        visit_ast(args_ast->stmts[i]);
        ir_insert(ir_last);
    }
    struct ir_node *args = ir_first;

    /// todo: Check if void return type.

    ir_first = saved_ir_first;
    ir_last = saved_ir_last;
    ir_prev = saved_ir_prev;
    ir_save_first = saved_ir_save_first;

    enum data_type ret_dt = ir_func_return_type(ast->name);

    if (ret_dt == D_T_VOID) {
        struct ir_node *call = ir_func_call_init(ast->name, args);
        ir_insert(call);
    } else {
        int32_t next_idx = ir_var_idx++;
        ir_last = ir_alloca_init(ret_dt, next_idx);
        ir_insert(ir_last);
        struct ir_node *call = ir_func_call_init(ast->name, args);
        ir_last = ir_store_call_init(next_idx, call);
        ir_insert(ir_last);
        ir_last = ir_sym_init(next_idx);
    }
}

/* static */ void visit_ast(struct ast_node *ast)
{
    assert(ast);

    void *ptr = ast->ast;
    switch (ast->type) {
    case AST_CHAR_LITERAL:    visit_ast_char(ptr); break;
    case AST_INTEGER_LITERAL: visit_ast_num(ptr); break;
    case AST_FLOATING_POINT_LITERAL: visit_ast_float(ptr); break;
    case AST_STRING_LITERAL:  visit_ast_string(ptr); break;
    case AST_BOOLEAN_LITERAL: visit_ast_bool(ptr); break;
    case AST_SYMBOL:          visit_ast_symbol(ptr); break;
    case AST_VAR_DECL:        visit_ast_var_decl(ptr); break;
    case AST_ARRAY_DECL:      visit_ast_array_decl(ptr); break;
    case AST_STRUCT_DECL:     visit_ast_struct_decl(ptr); break;
    case AST_BREAK_STMT:      visit_ast_break(ptr); break;
    case AST_CONTINUE_STMT:   visit_ast_continue(ptr); break;
    case AST_BINARY:          visit_ast_binary(ptr); break;
    case AST_PREFIX_UNARY:    visit_ast_unary(ptr); break;
    case AST_POSTFIX_UNARY:   visit_ast_unary(ptr); break;
    case AST_ARRAY_ACCESS:    visit_ast_array_access(ptr); break;
    case AST_MEMBER:          visit_ast_member(ptr); break;
    case AST_IF_STMT:         visit_ast_if(ptr); break;
    case AST_FOR_STMT:        visit_ast_for(ptr); break;
    case AST_WHILE_STMT:      visit_ast_while(ptr); break;
    case AST_DO_WHILE_STMT:   visit_ast_do_while(ptr); break;
    case AST_RETURN_STMT:     visit_ast_return(ptr); break;
    case AST_COMPOUND_STMT:   visit_ast_compound(ptr); break;
    case AST_FUNCTION_DECL:   visit_ast_function_decl(ptr); break;
    case AST_FUNCTION_CALL:   visit_ast_function_call(ptr); break;
    default:
        weak_unreachable("Wrong AST type (numeric: %d).", ast->type);
    }
}

struct ir_node *ir_gen(struct ast_node *ast)
{
    invalidate();

    visit_ast(ast);

    vector_foreach(ir_func_decls, i) {
        if (i >= ir_func_decls.count - 1)
            break;
        vector_at(ir_func_decls, i)->next =
        vector_at(ir_func_decls, i + 1);

        vector_at(ir_func_decls, i + 1)->prev =
        vector_at(ir_func_decls, i);
    }

    // ir_link(&ir);

    /// TODO: Collect first statement.
    return vector_at(ir_func_decls, 0);
}