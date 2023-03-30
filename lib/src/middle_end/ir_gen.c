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

static ir_array_t ir_stmts;
static ir_array_t ir_func_decls;
static ir_node_t  ir_last;
/// Used to count alloca instructions.
/// Conditions:
/// - reset at the start of each function declaration,
/// - increments with every created alloca instruction.
static int32_t    ir_var_idx;

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

static void visit_ast_binary(ast_binary_t *ast) { (void) ast; }

static void visit_ast_break(ast_break_t *ast) { (void) ast; }
static void visit_ast_continue(ast_continue_t *ast) { (void) ast; }

static void visit_ast_for(ast_for_t *ast) { (void) ast; }
static void visit_ast_while(ast_while_t *ast) { (void) ast; }
static void visit_ast_do_while(ast_do_while_t *ast) { (void) ast; }
static void visit_ast_if(ast_if_t *ast) { (void) ast; }

static void visit_ast_return(ast_return_t *ast)
{
    memset(&ir_last, 0, sizeof(ir_last));
    if (ast->operand) {
        visit_ast(ast->operand);
    }
    ir_last = ir_ret_init(/*is_void=*/! ( (bool) ast->operand ), ir_last);
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