/* ir_gen.c - IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_gen.h"
#include "middle_end/ir_storage.h"
#include "middle_end/ir.h"
#include "front_end/ast/ast.h"
#include "util/vector.h"
#include "util/unreachable.h"
#include <assert.h>
#include <string.h>

typedef vector_t(struct ir_node) ir_array_t;

/// Statements of current function. Every function
/// start to fill this array from scratch.
static ir_array_t      ir_stmts;
/// Total list of functions.
static ir_array_t      ir_func_decls;
/// Last generated opcode.
static struct ir_node  ir_last;
/// Used to count alloca instructions.
/// Conditions:
/// - reset at the start of each function declaration,
/// - increments with every created alloca instruction.
static int32_t         ir_var_idx;

static void invalidate()
{
    vector_free(ir_stmts);
    vector_free(ir_func_decls);
    memset(&ir_last, 0, sizeof (ir_last));
    ir_var_idx = 0;
}

static void visit_ast(struct ast_node *ast);

/// Primitives. Are not pushed to ir_stmts, because
/// they are immediate values.
static void visit_ast_bool(struct ast_bool *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_char(struct ast_char *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_float(struct ast_float *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_num(struct ast_num *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_string(struct ast_string *ast) { (void) ast; }

static void visit_ast_binary(struct ast_binary *ast)
{
    struct ir_node alloca = ir_alloca_init(D_T_INT, ir_var_idx++);
    int32_t   alloca_idx = ((struct ir_alloca *) alloca.ir)->idx;

    vector_push_back(ir_stmts, alloca);

    visit_ast(ast->lhs);
    struct ir_node lhs = ir_last;
    visit_ast(ast->rhs);
    struct ir_node rhs = ir_last;

    struct ir_node bin = ir_bin_init(ast->operation, lhs, rhs);
    ir_last = ir_store_bin_init(alloca_idx, bin);
    vector_push_back(ir_stmts, ir_last);
    ir_last = ir_sym_init(alloca_idx);
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
    if (ast->init) visit_ast(ast->init);

    /// Body starts with condition that is checked on each
    /// iteration.
    int32_t    next_iter_jump_idx = 0;
    struct ir_jump *exit_jmp_ptr = NULL;

    /// Condition is optional.
    if (ast->condition) {
        visit_ast(ast->condition);
        struct ir_node  cond_bin = ir_bin_init(TOK_NEQ, ir_last, ir_imm_init(0));
        struct ir_node  cond     = ir_cond_init(cond_bin, /*Not used for now.*/-1);
        struct ir_cond *cond_ptr = cond.ir;
        struct ir_node  exit_jmp = ir_jump_init(/*Not used for now.*/-1);
        next_iter_jump_idx       = ir_last.instr_idx;
        exit_jmp_ptr             = exit_jmp.ir;

        vector_push_back(ir_stmts, cond);
        vector_push_back(ir_stmts, exit_jmp);

        cond_ptr->goto_label = vector_back(ir_stmts).instr_idx + 1;
    } else {
        next_iter_jump_idx = ir_last.instr_idx + 1;
    }

    visit_ast(ast->body);
    /// Increment is optional.
    if (ast->increment) visit_ast(ast->increment);
    ir_last = ir_jump_init(next_iter_jump_idx);

    if (ast->condition)
        exit_jmp_ptr->idx = ir_last.instr_idx + 1;

    vector_push_back(ir_stmts, ir_last);
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

    visit_ast(ast->condition);
    struct ir_node  cond_bin      = ir_bin_init(TOK_NEQ, ir_last, ir_imm_init(0));
    struct ir_node  cond          = ir_cond_init(cond_bin, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr      = cond.ir;
    struct ir_node  exit_jmp      = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *exit_jmp_ptr  = exit_jmp.ir;
    int32_t         next_iter_idx = ir_last.instr_idx;

    vector_push_back(ir_stmts, cond);
    vector_push_back(ir_stmts, exit_jmp);

    cond_ptr->goto_label = vector_back(ir_stmts).instr_idx + 1;

    visit_ast(ast->body);

    struct ir_node next_iter_jmp = ir_jump_init(next_iter_idx);
    vector_push_back(ir_stmts, next_iter_jmp);

    exit_jmp_ptr->idx = next_iter_jmp.instr_idx + 1;
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

    if (vector_size(ir_stmts) == 0)
        stmt_begin = 0;
    else
        stmt_begin = vector_back(ir_stmts).instr_idx;

    visit_ast(ast->body);
    /// There we allocate temporary variable for
    /// comparison at the end of body.
    visit_ast(ast->condition);

    struct ir_node  cond_bin = ir_bin_init(TOK_NEQ, ir_last, ir_imm_init(0));
    struct ir_node  cond     = ir_cond_init(cond_bin, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr = cond.ir;

    vector_push_back(ir_stmts, cond);

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
        ir_last.type == IR_IMM ||
        ir_last.type == IR_SYM
    ) && ("Immediate value or symbol required."));
    /// Condition always looks like comparison with 0.
    ///
    /// Possible cases:
    ///                    v Binary operation result.
    /// - if (1 + 1) -> if sym neq $0 goto ...
    /// - if (1    ) -> if imm neq $0 goto ...
    /// - if (var  ) -> if sym neq $0 goto ...
    ir_last = ir_bin_init(TOK_NEQ, ir_last, ir_imm_init(0));

    struct ir_node  cond        = ir_cond_init(ir_last, /*Not used for now.*/-1);
    struct ir_cond *cond_ptr    = cond.ir;
    struct ir_node  end_jmp     = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *end_jmp_ptr = end_jmp.ir;

    /// Body starts after exit jump.
    cond_ptr->goto_label = end_jmp.instr_idx + 1;
    vector_push_back(ir_stmts, cond);
    vector_push_back(ir_stmts, end_jmp);

    visit_ast(ast->body);
    /// Even with code like
    /// void f() { if (x) { f(); } }
    /// this will make us to jump to the `ret`
    /// instruction, which terminates each (regardless
    /// on the return type) function.
    end_jmp_ptr->idx = ir_last.instr_idx + 1;

    if (!ast->else_body) return;
    struct ir_node  else_jmp = ir_jump_init(/*Not used for now.*/-1);
    struct ir_jump *else_jmp_ptr = else_jmp.ir;
    /// Index of this jump will be changed through pointer.
    vector_push_back(ir_stmts, else_jmp);

    /// Jump over the `then` statement to `else`.
    end_jmp_ptr->idx = ir_last.instr_idx
        + 1  /// Jump statement.
        + 1; /// The next one (first in `else` part).
    visit_ast(ast->else_body);
    /// `then` part ends with jump over `else` part.
    else_jmp_ptr->idx = ir_last.instr_idx + 1;
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
    vector_push_back(ir_stmts, ir_last);
}

static void visit_ast_symbol(struct ast_symbol *ast)
{
    int32_t idx = ir_storage_get(ast->value);
    ir_last = ir_sym_init(idx);
}

static void visit_ast_unary(struct ast_unary *ast)
{
    visit_ast(ast->operand);
    assert((
        ir_last.type == IR_SYM
    ) && ("Unary operator expects variable argument."));
    struct ir_sym *sym = ir_last.ir;

    switch (ast->operation) {
    case TOK_INC: ir_last = ir_bin_init(TOK_PLUS,  ir_last, ir_imm_init(1)); break;
    case TOK_DEC: ir_last = ir_bin_init(TOK_MINUS, ir_last, ir_imm_init(1)); break;
    default: weak_unreachable("Unknown unary operator.");
    }
    ir_last = ir_store_bin_init(sym->idx, ir_last);
    vector_push_back(ir_stmts, ir_last);
}

static void visit_ast_struct_decl(struct ast_struct_decl *ast) { (void) ast; }

static void visit_ast_var_decl(struct ast_var_decl *ast)
{
    int32_t next_idx = ir_var_idx++;
    ir_last = ir_alloca_init(ast->dt, next_idx);
    /// Used as function argument or as function body statement.
    vector_push_back(ir_stmts, ir_last);
    ir_storage_push(ast->name, next_idx);

    if (ast->body) {
        visit_ast(ast->body);

        switch (ir_last.type) {
        case IR_IMM: {
            struct ir_imm *imm = ir_last.ir;
            ir_last = ir_store_imm_init(next_idx, imm->imm);
            break;
        }
        case IR_SYM: {
            struct ir_sym *sym = ir_last.ir;
            ir_last = ir_store_var_init(next_idx, sym->idx);
            break;
        }
        default:
            weak_unreachable(
                "Expected symbol or immediate value as variable initializer."
	    );
        }
        vector_push_back(ir_stmts, ir_last);
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

    /// 1: Store function statements in ir_stmts
    /// 2: Save pointer to ir_stmts on end
    /// 3: ir_stmts = {0} (dispose allocated data)
    ir_var_idx = 0;
    memset(&ir_stmts, 0, sizeof (ir_stmts));
    visit_ast(decl->args);
    uint64_t args_size = ir_stmts.count;
    struct ir_node *args = ir_stmts.data;

    memset(&ir_stmts, 0, sizeof (ir_stmts));
    visit_ast(decl->body);
    if (decl->data_type == D_T_VOID) {
        struct ir_node op = ir_node_init(IR_RET_VOID, NULL);
        vector_push_back(ir_stmts, ir_ret_init(true, op));
    }
    uint64_t body_size = ir_stmts.count;
    struct ir_node *body = ir_stmts.data;

    vector_push_back(
        ir_func_decls,
        ir_func_decl_init(
            decl->name,
            args_size,
            args,
            body_size,
            body
        )
    );

    ir_storage_reset();
}

static void visit_ast_function_call(struct ast_function_call *ast) { (void) ast; }

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
        weak_unreachable("Wrong AST type");
    }
}

struct ir ir_gen(struct ast_node *ast)
{
    invalidate();
    visit_ast(ast);

    struct ir ir = {
        .decls      = ir_func_decls.data,
        .decls_size = ir_func_decls.count
    };
    return ir;
}

void ir_cleanup(struct ir *ir)
{
    for (uint64_t i = 0; i < ir->decls_size; ++i)
        ir_node_cleanup(ir->decls[i]);
}