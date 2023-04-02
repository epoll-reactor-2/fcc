/* ir_gen.c - IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_gen.h"
#include "middle_end/ir.h"
#include "front_end/ast/ast_array_access.h"
#include "front_end/ast/ast_array_decl.h"
#include "front_end/ast/ast_binary.h"
#include "front_end/ast/ast_break.h"
#include "front_end/ast/ast_bool.h"
#include "front_end/ast/ast_char.h"
#include "front_end/ast/ast_compound.h"
#include "front_end/ast/ast_continue.h"
#include "front_end/ast/ast_do_while.h"
#include "front_end/ast/ast_float.h"
#include "front_end/ast/ast_for.h"
#include "front_end/ast/ast_function_call.h"
#include "front_end/ast/ast_function_decl.h"
#include "front_end/ast/ast_if.h"
#include "front_end/ast/ast_member.h"
#include "front_end/ast/ast_node.h"
#include "front_end/ast/ast_num.h"
#include "front_end/ast/ast_return.h"
#include "front_end/ast/ast_string.h"
#include "front_end/ast/ast_struct_decl.h"
#include "front_end/ast/ast_symbol.h"
#include "front_end/ast/ast_unary.h"
#include "front_end/ast/ast_var_decl.h"
#include "front_end/ast/ast_while.h"
#include "utility/vector.h"
#include "utility/unreachable.h"
#include <assert.h>
#include <string.h>

typedef vector_t(ir_node_t) ir_array_t;

/// Statements of current function. Every function
/// start to fill this array from scratch.
static ir_array_t ir_stmts;
/// Total list of functions.
static ir_array_t ir_func_decls;
/// Last generated opcode.
static ir_node_t  ir_last;
/// Used to count alloca instructions.
/// Conditions:
/// - reset at the start of each function declaration,
/// - increments with every created alloca instruction.
static int32_t    ir_var_idx;

static void invalidate()
{
    vector_free(ir_stmts);
    vector_free(ir_func_decls);
    memset(&ir_last, 0, sizeof(ir_last));
    ir_var_idx = 0;
}

static void visit_ast(ast_node_t *ast);

/// Primitives. Are not pushed to ir_stmts, because
/// they are immediate values.
static void visit_ast_bool(ast_bool_t *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_char(ast_char_t *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_float(ast_float_t *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_num(ast_num_t *ast)
{
    ir_last = ir_imm_init(ast->value);
}

static void visit_ast_string(ast_string_t *ast) { (void) ast; }

static void visit_ast_binary(ast_binary_t *ast)
{
    ir_node_t alloca = ir_alloca_init(D_T_INT, ir_var_idx++);
    int32_t   alloca_idx = ((ir_alloca_t *) alloca.ir)->idx;

    vector_push_back(ir_stmts, alloca);

    visit_ast(ast->lhs);
    ir_node_t lhs = ir_last;
    visit_ast(ast->rhs);
    ir_node_t rhs = ir_last;

    ir_node_t bin = ir_bin_init(ast->operation, lhs, rhs);
    ir_last = ir_store_bin_init(alloca_idx, bin);
    vector_push_back(ir_stmts, ir_last);
    ir_last = ir_sym_init(alloca_idx);
}

static void visit_ast_break(ast_break_t *ast) { (void) ast; }
static void visit_ast_continue(ast_continue_t *ast) { (void) ast; }

static void visit_ast_for(ast_for_t *ast) { (void) ast; }
static void visit_ast_while(ast_while_t *ast) { (void) ast; }
static void visit_ast_do_while(ast_do_while_t *ast) { (void) ast; }

static void visit_ast_if(ast_if_t *ast)
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
    /// - if (1    ) -> if imm neq $0 goto ...
    ///
    ///                    v Binary operation result.
    /// - if (1 + 1) -> if sym neq $0 goto ...
    ///
    /// - if (var  ) -> if sym neq $0 goto ...
    ir_last = ir_bin_init(TOK_NEQ, ir_last, ir_imm_init(0));

    ir_node_t  cond = ir_cond_init(ir_last, /*Not used for now.*/-1);
    ir_cond_t *cond_ptr = cond.ir;

    ir_node_t  cond_false_jmp = ir_jump_init(/*Not used for now.*/-1);
    ir_jump_t *cond_false_jmp_ptr = cond_false_jmp.ir;

    /// Body starts after exit jump.
    cond_ptr->goto_label = cond_false_jmp.instr_idx + 1;
    vector_push_back(ir_stmts, cond);
    vector_push_back(ir_stmts, cond_false_jmp);

    visit_ast(ast->body);
    /// Even with code like
    /// void f() { if (x) { f(); } }
    /// this will make us to jump to the `ret`
    /// instruction, which terminates each (regardless
    /// on the return type) function.
    cond_false_jmp_ptr->idx = ir_last.instr_idx + 1;

    if (!ast->else_body) return;
    ir_node_t  end_jmp = ir_jump_init(/*Not used for now.*/-1);
    ir_jump_t *end_jmp_ptr = end_jmp.ir;
    /// Will be changed through ptr.
    vector_push_back(ir_stmts, end_jmp);

    /// Jump over the `then` statement to `else`.
    cond_false_jmp_ptr->idx = ir_last.instr_idx
        + 1  /// Jump statement.
        + 1; /// The next one (first in `else` part).
    visit_ast(ast->else_body);
    /// `then` part ends with jump over `else` part.
    end_jmp_ptr->idx = ir_last.instr_idx + 1;
}

static void visit_ast_return(ast_return_t *ast)
{
    memset(&ir_last, 0, sizeof(ir_last));
    if (ast->operand) {
        visit_ast(ast->operand);
    }
    ir_last = ir_ret_init(
        /*is_void=*/! ( (bool) ast->operand ),
        /*op=*/ir_last
    );
    vector_push_back(ir_stmts, ir_last);
}

static void visit_ast_symbol(ast_symbol_t *ast) { (void) ast; }
static void visit_ast_unary(ast_unary_t *ast) { (void) ast; }
static void visit_ast_struct_decl(ast_struct_decl_t *ast) { (void) ast; }

static void visit_ast_var_decl(ast_var_decl_t *ast)
{
    ir_last = ir_alloca_init(ast->dt, ir_var_idx++);
    /// Used as function argument or as function body statement.
    vector_push_back(ir_stmts, ir_last);
}

static void visit_ast_array_decl(ast_array_decl_t *ast) { (void) ast; }
static void visit_ast_array_access(ast_array_access_t *ast) { (void) ast; }
static void visit_ast_member(ast_member_t *ast) { (void) ast; }

static void visit_ast_compound(ast_compound_t *ast)
{
    for (uint64_t i = 0; i < ast->size; ++i)
        visit_ast(ast->stmts[i]);
}

static void visit_ast_function_decl(ast_function_decl_t *decl)
{
    /// [1] Store function statements in ir_stmts
    /// [2] Save pointer to ir_stmts on end
    /// [3] ir_stmts = {0} (dispose allocated data)
    ir_var_idx = 0;
    memset(&ir_stmts, 0, sizeof(ir_stmts));
    visit_ast(decl->args);
    uint64_t   args_size = ir_stmts.count;
    ir_node_t *args      = ir_stmts.data;

    memset(&ir_stmts, 0, sizeof(ir_stmts));
    visit_ast(decl->body);
    if (decl->data_type == D_T_VOID) {
        ir_node_t op = ir_node_init(IR_RET_VOID, NULL);
        vector_push_back(ir_stmts, ir_ret_init(true, op));
    }
    uint64_t   body_size = ir_stmts.count;
    ir_node_t *body      = ir_stmts.data;

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
}

static void visit_ast_function_call(ast_function_call_t *ast) { (void) ast; }

/* static */ void visit_ast(ast_node_t *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_CHAR_LITERAL:
        visit_ast_char(ast->ast);
        break;
    case AST_INTEGER_LITERAL:
        visit_ast_num(ast->ast);
        break;
    case AST_FLOATING_POINT_LITERAL:
        visit_ast_float(ast->ast);
        break;
    case AST_STRING_LITERAL:
        visit_ast_string(ast->ast);
        break;
    case AST_BOOLEAN_LITERAL:
        visit_ast_bool(ast->ast);
        break;
    case AST_SYMBOL:
        visit_ast_symbol(ast->ast);
        break;
    case AST_VAR_DECL:
        visit_ast_var_decl(ast->ast);
        break;
    case AST_ARRAY_DECL:
        visit_ast_array_decl(ast->ast);
        break;
    case AST_STRUCT_DECL:
        visit_ast_struct_decl(ast->ast);
        break;
    case AST_BREAK_STMT:
        visit_ast_break(ast->ast);
        break;
    case AST_CONTINUE_STMT:
        visit_ast_continue(ast->ast);
        break;
    case AST_BINARY:
        visit_ast_binary(ast->ast);
        break;
    case AST_PREFIX_UNARY:
        visit_ast_unary(ast->ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_ast_unary(ast->ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_ast_array_access(ast->ast);
        break;
    case AST_MEMBER:
        visit_ast_member(ast->ast);
        break;
    case AST_IF_STMT:
        visit_ast_if(ast->ast);
        break;
    case AST_FOR_STMT:
        visit_ast_for(ast->ast);
        break;
    case AST_WHILE_STMT:
        visit_ast_while(ast->ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_ast_do_while(ast->ast);
        break;
    case AST_RETURN_STMT:
        visit_ast_return(ast->ast);
        break;
    case AST_COMPOUND_STMT:
        visit_ast_compound(ast->ast);
        break;
    case AST_FUNCTION_DECL:
        visit_ast_function_decl(ast->ast);
        break;
    case AST_FUNCTION_CALL:
        visit_ast_function_call(ast->ast);
        break;
    default:
        weak_unreachable("Wrong AST type");
    }
}

ir_t ir_gen(ast_node_t *ast)
{
    invalidate();
    visit_ast(ast);

    ir_t ir = {
        .decls      = ir_func_decls.data,
        .decls_size = ir_func_decls.count
    };
    return ir;
}

void ir_cleanup(ir_t *ir)
{
    for (uint64_t i = 0; i < ir->decls_size; ++i)
        ir_node_cleanup(ir->decls[i]);
}