/* functions_analysis.h - Function analyzer.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/analysis/ast_storage.h"
#include "front_end/ast/ast.h"
#include "util/diagnostic.h"
#include "util/unreachable.h"
#include <assert.h>
#include <stdint.h>
#include <string.h>

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
    memset(&last_ret, 0, sizeof (last_ret));
}

/// \note Interesting in this context things are only in the
///       conditional and iteration statements body, not in
///       the conditions.
static void visit_ast_node(struct ast_node *ast);

static void visit_ast_compound(struct ast_node *ast)
{
    struct ast_compound *stmt = ast->ast;
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit_ast_node(stmt->stmts[i]);
}

static void visit_ast_if(struct ast_node *ast)
{
    struct ast_if *stmt = ast->ast;
    visit_ast_node(stmt->body);
    if (stmt->else_body)
        visit_ast_node(stmt->else_body);
}

static void visit_ast_for(struct ast_node *ast)
{
    struct ast_for *stmt = ast->ast;
    visit_ast_node(stmt->body);
}

static void visit_ast_while(struct ast_node *ast)
{
    struct ast_while *stmt = ast->ast;
    visit_ast_node(stmt->body);
}

static void visit_ast_do_while(struct ast_node *ast)
{
    struct ast_do_while *stmt = ast->ast;
    visit_ast_node(stmt->body);
}

static void visit_ast_return(struct ast_node *ast)
{
    struct ast_return *stmt = ast->ast;
    if (stmt->operand) {
        visit_ast_node(stmt->operand);
        last_ret.line_no = ast->line_no;
        last_ret.col_no = ast->col_no;
        last_ret.occurred = true;
    }
}

static void visit_ast_function_decl(struct ast_node *ast)
{
    struct ast_function_decl *decl = ast->ast;
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

static void visit_ast_function_call(struct ast_node *ast)
{
    struct ast_function_call *stmt = ast->ast;
    struct ast_function_decl *fun = ast_storage_lookup(stmt->name)->ast->ast;
    struct ast_compound *call_args = stmt->args->ast;
    struct ast_compound *decl_args = fun->args->ast;

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

void visit_ast_node(struct ast_node *ast)
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
    case AST_MEMBER: /// Unused.
        break;
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

void analysis_functions_analysis(struct ast_node *root)
{
    ast_storage_init_state();
    visit_ast_node(root);
    reset_internal_state();
    ast_storage_reset_state();
}