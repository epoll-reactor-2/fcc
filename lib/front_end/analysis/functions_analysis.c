/* functions_analysis.h - Function analyzer.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/analysis/ast_storage.h"
#include "front_end/ast/ast_array_access.h"
#include "front_end/ast/ast_binary.h"
#include "front_end/ast/ast_do_while.h"
#include "front_end/ast/ast_for.h"
#include "front_end/ast/ast_function_call.h"
#include "front_end/ast/ast_function_decl.h"
#include "front_end/ast/ast_if.h"
#include "front_end/ast/ast_member.h"
#include "front_end/ast/ast_node.h"
#include "front_end/ast/ast_return.h"
#include "front_end/ast/ast_symbol.h"
#include "front_end/ast/ast_unary.h"
#include "front_end/ast/ast_var_decl.h"
#include "front_end/ast/ast_while.h"
#include "utility/diagnostic.h"
#include "utility/unreachable.h"
#include <assert.h>
#include <stdint.h>

/// Last return occurence context.
///
/// \pre All fields set to 0 at the start
///      of each function.
static struct {
    uint16_t line_no;
    uint16_t col_no;
    bool     occurred;
} last_ret = {0};

static void reset_internal_state()
{
    last_ret.col_no = 0;
    last_ret.line_no = 0;
    last_ret.occurred = false;
}

/// \note Interesting in this context things are only in the
///       conditional and iteration statements body, not in
///       the conditions.
static void visit_ast_node(ast_node_t *ast);

static void visit_ast_compound(ast_node_t *ast)
{
    ast_compound_t *stmt = ast->ast;
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit_ast_node(stmt->stmts[i]);
}

static void visit_ast_if(ast_node_t *ast)
{
    ast_if_t *stmt = ast->ast;
    visit_ast_node(stmt->body);
    if (stmt->else_body)
        visit_ast_node(stmt->else_body);
}

static void visit_ast_for(ast_node_t *ast)
{
    ast_for_t *stmt = ast->ast;
    visit_ast_node(stmt->body);
}

static void visit_ast_while(ast_node_t *ast)
{
    ast_while_t *stmt = ast->ast;
    visit_ast_node(stmt->body);
}

static void visit_ast_do_while(ast_node_t *ast)
{
    ast_do_while_t *stmt = ast->ast;
    visit_ast_node(stmt->body);
}

static void visit_ast_return(ast_node_t *ast)
{
    ast_return_t *stmt = ast->ast;
    if (stmt->operand) {
        visit_ast_node(stmt->operand);
        last_ret.line_no = ast->line_no;
        last_ret.col_no = ast->col_no;
        last_ret.occurred = true;
    }
}

static void visit_ast_function_decl(ast_node_t *ast)
{
    ast_function_decl_t *decl = ast->ast;
    ast_storage_push(decl->name, ast);
    /// Don't need to analyze arguments though.
    visit_ast_node(decl->body);

    uint16_t line_no = last_ret.line_no;
    uint16_t col_no = last_ret.col_no;

    if (last_ret.occurred && decl->data_type == D_T_VOID) {
        reset_internal_state();
        weak_compile_error(
            line_no, col_no,
            "Cannot return value from void function"
        );
    }

    if (!last_ret.occurred && decl->data_type != D_T_VOID) {
        reset_internal_state();
        weak_compile_error(
            ast->line_no, ast->col_no,
            "Expected return value"
        );
    }
}

static void visit_ast_function_call(ast_node_t *ast)
{
    ast_function_call_t *stmt = ast->ast;
    ast_function_decl_t *fun = ast_storage_lookup(stmt->name)->ast->ast;
    ast_compound_t *call_args = stmt->args->ast;
    ast_compound_t *decl_args = fun->args->ast;

    if (call_args->size != decl_args->size)
        weak_compile_error(
            ast->line_no,
            ast->col_no,
            "Arguments size mismatch: %u got, but %u expected",
            call_args->size,
            decl_args->size
        );

    for (uint64_t i = 0; i < call_args->size; ++i)
        visit_ast_node(call_args->stmts[i]);
}

void visit_ast_node(ast_node_t *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_CHAR_LITERAL: /// Unused.
    case AST_INTEGER_LITERAL: /// Unused.
    case AST_FLOATING_POINT_LITERAL: /// Unused.
    case AST_STRING_LITERAL: /// Unused.
    case AST_BOOLEAN_LITERAL: /// Unused.
    case AST_STRUCT_DECL: /// Unused.
    case AST_BREAK_STMT: /// Unused.
    case AST_CONTINUE_STMT: /// Unused.
    case AST_VAR_DECL: /// Unused.
    case AST_SYMBOL: /// Unused.
    case AST_ARRAY_DECL: /// Unused.
    case AST_BINARY: /// Unused.
    case AST_PREFIX_UNARY: /// Unused.
    case AST_POSTFIX_UNARY: /// Unused.
    case AST_ARRAY_ACCESS: /// Unused.
    case AST_MEMBER: break; /// Unused.
    case AST_COMPOUND_STMT:
        visit_ast_compound(ast);
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

void analysis_functions_analysis(ast_node_t *root)
{
    ast_storage_init_state();
    visit_ast_node(root);
    reset_internal_state();
    ast_storage_reset_state();
}