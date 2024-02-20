/* fn_ana.c - Function analyzer.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/ana.h"
#include "front_end/ana/fn_storage.h"
#include "front_end/ast/ast.h"
#include "util/diagnostic.h"
#include "util/hashmap.h"
#include "util/unreachable.h"
#include "builtins.h"
#include <assert.h>
#include <string.h>

/* Last return occurrence context.

   \pre All fields set to 0 at the start
        of each function. */
static struct {
    uint16_t line_no;
    uint16_t col_no;
    bool     occurred;
} last_ret = {0};

static fn_storage_t fn_storage;

static void init()
{
    memset(&last_ret, 0, sizeof (last_ret));
    fn_storage_init(&fn_storage);
}

static void reset()
{
    fn_storage_free(&fn_storage);
}

/* \note Interesting in this context things are only in the
         conditional and iteration statements body, not in
         the conditions. */
static void visit(struct ast_node *ast);

static void visit_compound(struct ast_node *ast)
{
    struct ast_compound *stmt = ast->ast;
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit(stmt->stmts[i]);
}

static void visit_if(struct ast_node *ast)
{
    struct ast_if *stmt = ast->ast;
    visit(stmt->body);
    if (stmt->else_body)
        visit(stmt->else_body);
}

static void visit_for(struct ast_node *ast)
{
    struct ast_for *stmt = ast->ast;
    visit(stmt->body);
}

static void visit_while(struct ast_node *ast)
{
    struct ast_while *stmt = ast->ast;
    visit(stmt->body);
}

static void visit_do_while(struct ast_node *ast)
{
    struct ast_do_while *stmt = ast->ast;
    visit(stmt->body);
}

static void visit_return(struct ast_node *ast)
{
    struct ast_ret *stmt = ast->ast;
    if (stmt->op) {
        visit(stmt->op);
        last_ret.line_no = ast->line_no;
        last_ret.col_no = ast->col_no;
        last_ret.occurred = true;
    }
}

static void visit_fn_decl(struct ast_node *ast)
{
    struct ast_fn_decl *decl = ast->ast;
    fn_storage_push(&fn_storage, decl->name, decl);
    /* Don't need to analyze arguments though. */
    visit(decl->body);

    uint16_t line_no = last_ret.line_no;
    uint16_t col_no = last_ret.col_no;

    if (last_ret.occurred && decl->data_type == D_T_VOID) {
        reset();
        weak_compile_error(
            line_no, col_no,
            "Cannot return value from void function"
        );
    }

    if (!last_ret.occurred && decl->data_type != D_T_VOID) {
        reset();
        weak_compile_error(
            ast->line_no, ast->col_no,
            "Expected return value"
        );
    }
}

static void visit_fn_call(struct ast_node *ast)
{
    struct ast_fn_call  *stmt      = ast->ast;
    struct builtin_fn   *fn        = fn_storage_lookup(&fn_storage, stmt->name);
    struct ast_compound *call_args = stmt->args->ast;

    if (call_args->size != fn->args_cnt)
        weak_compile_error(
            ast->line_no,
            ast->col_no,
            "Arguments size mismatch: %u got, but %u expected",
            call_args->size,
            fn->args_cnt
        );

    for (uint64_t i = 0; i < call_args->size; ++i)
        visit(call_args->stmts[i]);
}

static void visit_cast(struct ast_node *ast)
{
    struct ast_implicit_cast *cast = ast->ast;
    visit(cast->body);
}

void visit(struct ast_node *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_CHAR_LITERAL: /* Unused. */
    case AST_INTEGER_LITERAL: /* Unused. */
    case AST_FLOATING_POINT_LITERAL: /* Unused. */
    case AST_STRING_LITERAL: /* Unused. */
    case AST_BOOLEAN_LITERAL: /* Unused. */
    case AST_STRUCT_DECL: /* Unused. */
    case AST_BREAK_STMT: /* Unused. */
    case AST_CONTINUE_STMT: /* Unused. */
    case AST_VAR_DECL: /* Unused. */
    case AST_SYMBOL: /* Unused. */
    case AST_ARRAY_DECL: /* Unused. */
    case AST_BINARY: /* Unused. */
    case AST_PREFIX_UNARY: /* Unused. */
    case AST_POSTFIX_UNARY: /* Unused. */
    case AST_ARRAY_ACCESS: /* Unused. */
    case AST_MEMBER: /* Unused. */
        break;
    case AST_COMPOUND_STMT:
        visit_compound(ast);
        break;
    case AST_IF_STMT:
        visit_if(ast);
        break;
    case AST_FOR_STMT:
        visit_for(ast);
        break;
    case AST_WHILE_STMT:
        visit_while(ast);
        break;
    case AST_DO_WHILE_STMT:
        visit_do_while(ast);
        break;
    case AST_RETURN_STMT:
        visit_return(ast);
        break;
    case AST_FUNCTION_DECL:
        visit_fn_decl(ast);
        break;
    case AST_FUNCTION_CALL:
        visit_fn_call(ast);
        break;
    case AST_IMPLICIT_CAST:
        visit_cast(ast);
        break;
    default: {
        enum ast_type t = ast->type;
        weak_unreachable("Unknown AST type (%d, %s).", t, ast_type_to_string(t));
    }
    }
}

void ana_fn(struct ast_node *root)
{
    init();
    visit(root);
    reset();
}