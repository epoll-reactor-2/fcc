/* type_analysis.h - Type checker.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/analysis/ast_storage.h"
#include "front_end/ast/ast_array_access.h"
#include "front_end/ast/ast_array_decl.h"
#include "front_end/ast/ast_binary.h"
#include "front_end/ast/ast_bool.h"
#include "front_end/ast/ast_char.h"
#include "front_end/ast/ast_do_while.h"
#include "front_end/ast/ast_float.h"
#include "front_end/ast/ast_for.h"
#include "front_end/ast/ast_function_call.h"
#include "front_end/ast/ast_function_decl.h"
#include "front_end/ast/ast_if.h"
#include "front_end/ast/ast_member.h"
#include "front_end/ast/ast_num.h"
#include "front_end/ast/ast_return.h"
#include "front_end/ast/ast_string.h"
#include "front_end/ast/ast_symbol.h"
#include "front_end/ast/ast_unary.h"
#include "front_end/ast/ast_var_decl.h"
#include "front_end/ast/ast_while.h"
#include "utility/diagnostic.h"
#include "utility/lexical.h"
#include "utility/unreachable.h"
#include <assert.h>

static data_type_e last_dt = D_T_UNKNOWN;
static data_type_e last_return_dt = D_T_UNKNOWN;

static void reset_internal_state()
{
    last_dt = D_T_UNKNOWN;
    last_return_dt = D_T_UNKNOWN;
}

static void visit_ast_node(ast_node_t *ast);

static void visit_ast_char  () { last_dt = D_T_CHAR; }
static void visit_ast_num   () { last_dt = D_T_INT; }
static void visit_ast_float () { last_dt = D_T_FLOAT; }
static void visit_ast_string() { last_dt = D_T_STRING; }
static void visit_ast_bool  () { last_dt = D_T_BOOL; }

static bool is_correct_bin_op(tok_type_e op, data_type_e t)
{
    bool are_correct = false;

    switch (op) {
    case TOK_ASSIGN: /// Fall through.
        /// We need only check if there are same types on assignment.
        are_correct = true;
        break;
    /// Integer and floats.
    case TOK_PLUS:
    case TOK_MINUS:
    case TOK_STAR:
    case TOK_SLASH:
    case TOK_LE:
    case TOK_LT:
    case TOK_GE:
    case TOK_GT:
    case TOK_EQ:
    case TOK_NEQ:
    case TOK_OR:
    case TOK_AND:
    case TOK_MUL_ASSIGN:
    case TOK_DIV_ASSIGN:
    case TOK_PLUS_ASSIGN:
    case TOK_MINUS_ASSIGN: /// Fall through.
        are_correct |= t == D_T_INT;
        are_correct |= t == D_T_CHAR;
        are_correct |= t == D_T_BOOL;
        are_correct |= t == D_T_FLOAT;
        break;
    /// Only integers.
    case TOK_BIT_OR:
    case TOK_BIT_AND:
    case TOK_XOR:
    case TOK_SHL:
    case TOK_SHR:
    case TOK_MOD:
    case TOK_MOD_ASSIGN:
    case TOK_BIT_OR_ASSIGN:
    case TOK_BIT_AND_ASSIGN:
    case TOK_XOR_ASSIGN:
    case TOK_SHL_ASSIGN:
    case TOK_SHR_ASSIGN: /// Fall through.
        are_correct |= t == D_T_INT;
        are_correct |= t == D_T_CHAR;
        are_correct |= t == D_T_BOOL;
        break;
    default:
        break;
    }

    return are_correct;
}

static void visit_ast_binary(ast_node_t *ast)
{
    ast_binary_t *stmt = ast->ast;
    visit_ast_node(stmt->lhs);
    data_type_e l_dt = last_dt;
    visit_ast_node(stmt->rhs);
    data_type_e r_dt = last_dt;

    bool are_same = false;
    are_same |= l_dt == D_T_BOOL && r_dt == D_T_BOOL;
    are_same |= l_dt == D_T_CHAR && r_dt == D_T_CHAR;
    are_same |= l_dt == D_T_FLOAT && r_dt == D_T_FLOAT;
    are_same |= l_dt == D_T_INT && r_dt == D_T_INT;

    bool correct_ops = is_correct_bin_op(stmt->operation, l_dt);
    if (!are_same || !correct_ops)
        weak_compile_error(
            ast->line_no,
            ast->col_no,
            "Cannot apply `%s` to %s and %s",
            tok_to_string(stmt->operation),
            data_type_to_string(l_dt),
            data_type_to_string(r_dt)
        );
}

static void visit_ast_unary(ast_node_t *ast)
{
    ast_unary_t *stmt = ast->ast;
    visit_ast_node(stmt->operand);
    data_type_e dt = last_dt;

    switch (stmt->operation) {
    case TOK_INC:
    case TOK_DEC: /// Fall through.
        if (dt != D_T_CHAR && dt != D_T_INT)
            weak_compile_error(
                ast->line_no,
                ast->col_no,
                "Cannot apply `%s` to %s",
                tok_to_string(stmt->operation),
                data_type_to_string(dt)
            );
        break;
    case TOK_BIT_AND: /// Address operator `&`.
    case TOK_STAR: /// Dereference operator `*`.
        /// Should not analyze anything because operands
        /// of unary operator are checked in parser.
        break;
    default:
        weak_unreachable("Invalid unary operand.");
    }
}

static void visit_ast_symbol(ast_node_t *ast)
{
    ast_symbol_t *stmt = ast->ast;
    last_dt = ast_storage_lookup(stmt->value)->data_type;
}

static void visit_ast_var_decl(ast_node_t *ast)
{
    ast_var_decl_t *decl = ast->ast;
    if (decl->body) {
        visit_ast_node(decl->body);
        if (decl->dt != last_dt)
            weak_compile_error(
                ast->line_no,
                ast->col_no,
                "Cannot assign %s to variable of type %s",
                data_type_to_string(last_dt),
                data_type_to_string(decl->dt)
            );
    }
    ast_storage_push_typed(decl->name, decl->dt, ast);
    last_dt = decl->dt;
}

static void visit_ast_array_decl(ast_node_t *ast)
{
    ast_array_decl_t *decl = ast->ast;
    /// Required to be compound.
    ast_compound_t *dimensions = decl->arity_list->ast;
    for (uint64_t i = 0; i < dimensions->size; ++i) {
        int32_t num = ( (ast_num_t *)(dimensions->stmts[i]->ast) )->value;
        if (num == 0)
            weak_compile_error(
                ast->line_no,
                ast->col_no,
                "Array size cannot be equal '0'"
            );
    }

    ast_storage_push_typed(decl->name, decl->dt, ast);
    last_dt = decl->dt;
}

#define MIN(a, b) ((a) < (b) ? (a) : (b))
static void out_of_range_analysis(ast_node_t *decl_indices_ast, ast_node_t *indices_ast)
{
    ast_compound_t *call_indices = indices_ast->ast;
    ast_compound_t *decl_indices = decl_indices_ast->ast;
    assert(call_indices->size);
    assert(decl_indices->size);
    if (decl_indices->size < call_indices->size) {
        char index[16];
        ordinal_numeral(call_indices->size, index);
        weak_compile_error(
            call_indices->stmts[0]->line_no,
            call_indices->stmts[0]->col_no,
            "Cannot get %s index of %d dimensional array",
            index, decl_indices->size
        );
    }

    for (uint64_t i = 0; i < MIN(call_indices->size, decl_indices->size); ++i) {
        if (call_indices->stmts[i]->type != AST_INTEGER_LITERAL)
            continue;
        ast_node_t *index_ast = call_indices->stmts[i];
        ast_num_t *num = index_ast->ast;
        ast_num_t *decl_index_ast = decl_indices->stmts[i]->ast;
        int32_t index = num->value;
        int32_t decl_index = decl_index_ast->value;

        if (index < 0)
            weak_compile_error(
                index_ast->line_no,
                index_ast->col_no,
                "Array index less than zero"
            );

        if (index >= decl_index)
            weak_compile_error(
                index_ast->line_no,
                index_ast->col_no,
                "Out of range! Index (which is %d) >= array size (which is %d)",
                index, decl_index
            );
    }
}
#undef MIN

static void visit_ast_array_access(ast_node_t *ast)
{
    ast_array_access_t *stmt = ast->ast;
    ast_node_t *record = ast_storage_lookup(stmt->name)->ast;

    if (record->type != AST_ARRAY_DECL) {
        /// If it is not an array, then obviously variable
        /// declaration.
        ast_var_decl_t *decl = record->ast;
        if (decl->indirection_lvl == 0)
            weak_compile_error(
                ast->line_no,
                ast->col_no,
                "Cannot get index of non-array type"
            );
        last_dt = decl->dt;
    } else {
        ast_array_decl_t *decl = record->ast;
        out_of_range_analysis(decl->arity_list, stmt->indices);
    }
    ast_compound_t *arity = stmt->indices->ast;
    for (uint64_t i = 0; i < arity->size; ++i) {
        visit_ast_node(arity->stmts[i]);
        if (last_dt != D_T_INT)
            weak_compile_error(
                arity->stmts[i]->line_no,
                arity->stmts[i]->col_no,
                "Expected integer as array index, got %s",
                data_type_to_string(last_dt)
            );
    }
}

static void require_last_dt_convertible_to_bool(ast_node_t *location)
{
    data_type_e dt = last_dt;
    if (dt != D_T_INT && dt != D_T_BOOL)
        weak_compile_error(
            location->line_no,
            location->col_no,
            "Cannot convert %s to boolean",
            data_type_to_string(dt)
        );
}

static void visit_ast_if(ast_node_t *ast)
{
    ast_if_t *stmt = ast->ast;
    visit_ast_node(stmt->condition);
    require_last_dt_convertible_to_bool(ast);

    visit_ast_node(stmt->body);
    if (stmt->else_body)
        visit_ast_node(stmt->else_body);
}

static void visit_ast_for(ast_node_t *ast)
{
    ast_for_t *stmt = ast->ast;
    if (stmt->init)
        visit_ast_node(stmt->init);
    if (stmt->condition) {
        visit_ast_node(stmt->condition);
        require_last_dt_convertible_to_bool(ast);
    }
    if (stmt->increment)
        visit_ast_node(stmt->increment);
    visit_ast_node(stmt->body);
}

static void visit_ast_while(ast_node_t *ast)
{
    ast_while_t *stmt = ast->ast;
    visit_ast_node(stmt->condition);
    require_last_dt_convertible_to_bool(ast);
    visit_ast_node(stmt->body);
}

static void visit_ast_do_while(ast_node_t *ast)
{
    ast_do_while_t *stmt = ast->ast;
    visit_ast_node(stmt->body);
    visit_ast_node(stmt->condition);
    require_last_dt_convertible_to_bool(ast);
}

static void visit_ast_return(ast_node_t *ast)
{
    ast_return_t *stmt = ast->ast;
    if (stmt->operand)
        visit_ast_node(stmt->operand);
    last_return_dt = last_dt;
}

static void visit_ast_compound(ast_node_t *ast)
{
    ast_compound_t *stmt = ast->ast;
    ast_storage_start_scope();
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit_ast_node(stmt->stmts[i]);
    ast_storage_end_scope();
}

static char *decl_name(ast_node_t *decl)
{
    if (decl->type == AST_VAR_DECL)
        return ( (ast_var_decl_t *)decl->ast )->name;

    if (decl->type == AST_ARRAY_DECL)
        return ( (ast_array_decl_t *)decl->ast )->name;

    weak_unreachable("Declaration expected");
}

static void visit_ast_function_call(ast_node_t *ast)
{
    ast_function_call_t *call = ast->ast;
    ast_node_t *decl = ast_storage_lookup(call->name)->ast;
    if (decl->type != AST_FUNCTION_DECL)
        weak_compile_error(
            ast->line_no,
            ast->col_no,
            "`%s` is not a function",
            call->name
        );

    ast_function_decl_t *fun = decl->ast;
    ast_compound_t *fun_args = fun->args->ast;
    ast_compound_t *call_args = call->args->ast;
    assert(
        fun_args->size == call_args->size &&
        "Call arguments size checked in function analyzer."
    );

    for (uint64_t i = 0; i < call_args->size; ++i) {
        visit_ast_node(fun_args->stmts[i]);
        data_type_e l_dt = last_dt;
        visit_ast_node(call_args->stmts[i]);
        data_type_e r_dt = last_dt;
        if (l_dt != r_dt)
            weak_compile_error(
                call_args->stmts[i]->line_no,
                call_args->stmts[i]->col_no,
                "For argument `%s` got %s, but %s expected",
                decl_name(fun_args->stmts[i]),
                data_type_to_string(r_dt),
                data_type_to_string(l_dt)
            );
    }
    last_dt = fun->data_type;
}

static void visit_ast_function_decl(ast_node_t *ast)
{
    ast_function_decl_t *decl = ast->ast;
    data_type_e dt = decl->data_type;
    if (decl->body == NULL) { /// Function prototype.
        ast_storage_push_typed(decl->name, D_T_FUNC, ast);
        return;
    }
    ast_storage_start_scope();
    /// This is to have function in recursive calls.
    ast_storage_push_typed(decl->name, D_T_FUNC, ast);
    /// Don't just visit compound AST, which creates and terminates scope.
    ast_compound_t *args = decl->args->ast;
    for (uint64_t i = 0; i < args->size; ++i)
        visit_ast_node(args->stmts[i]);

    visit_ast_node(decl->body);
    if (dt != D_T_VOID && dt != last_return_dt)
        weak_compile_error(
            ast->line_no,
            ast->col_no,
            "Cannot return %s instead of %s",
            data_type_to_string(last_return_dt),
            data_type_to_string(dt)
        );
    ast_storage_end_scope();
    /// This is to have function outside.
    ast_storage_push_typed(decl->name, D_T_FUNC, ast);
}

void visit_ast_node(ast_node_t *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_MEMBER: /// Unused... Or should be used?
    case AST_STRUCT_DECL: /// Unused... Or should be used?
    case AST_BREAK_STMT: /// Unused.
    case AST_CONTINUE_STMT: break; /// Unused.
    case AST_CHAR_LITERAL:
        visit_ast_char();
        break;
    case AST_INTEGER_LITERAL:
        visit_ast_num();
        break;
    case AST_FLOATING_POINT_LITERAL:
        visit_ast_float();
        break;
    case AST_STRING_LITERAL:
        visit_ast_string();
        break;
    case AST_BOOLEAN_LITERAL:
        visit_ast_bool();
        break;
    case AST_SYMBOL:
        visit_ast_symbol(ast);
        break;
    case AST_VAR_DECL:
        visit_ast_var_decl(ast);
        break;
    case AST_ARRAY_DECL:
        visit_ast_array_decl(ast);
        break;
    case AST_BINARY:
        visit_ast_binary(ast);
        break;
    case AST_PREFIX_UNARY:
        visit_ast_unary(ast);
        break;
    case AST_POSTFIX_UNARY:
        visit_ast_unary(ast);
        break;
    case AST_ARRAY_ACCESS:
        visit_ast_array_access(ast);
        break;
    case AST_IF_STMT:
        visit_ast_if(ast);
        break;
    case AST_FOR_STMT:
        visit_ast_for(ast);
        break;
    case AST_WHILE_STMT:
        visit_ast_while(ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_ast_do_while(ast);
        break;
    case AST_RETURN_STMT:
        visit_ast_return(ast);
        break;
    case AST_COMPOUND_STMT:
        visit_ast_compound(ast);
        break;
    case AST_FUNCTION_DECL:
        visit_ast_function_decl(ast);
        break;
    case AST_FUNCTION_CALL:
        visit_ast_function_call(ast);
        break;
    default:
        weak_unreachable("Wrong AST type");
    }
}

void analysis_type_analysis(ast_node_t *root)
{
    ast_storage_init_state();
    visit_ast_node(root);
    reset_internal_state();
    ast_storage_reset_state();
}
