/* dead_ana.c - Experiments on dead code detection.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

/* TODO: Design algorithm, evaluate all expressions. */

#include "front_end/ana/ana.h"
#include "front_end/ast/ast.h"
#include "front_end/ana/ast_storage.h"
#include "front_end/ast/ast_dump.h"
#include "util/diagnostic.h"
#include "util/unreachable.h"
#include <assert.h>

static void init()
{}

static void reset()
{}

/**********************************************
 **           Tree traversal                 **
 **********************************************/

static void visit(struct ast_node *ast);

static void visit_compound(struct ast_compound *stmt)
{
    for (uint64_t i = 0; i < stmt->size; ++i)
        visit(stmt->stmts[i]);
}

static void visit_fn_decl(struct ast_fn_decl *decl)
{
    struct ast_compound *args = decl->args->ast;
    for (uint64_t i = 0; i < args->size; ++i)
        visit(args->stmts[i]);
    visit(decl->body);
}

/**********************************************
 **         Condition evaluation             **
 **********************************************/

static bool scan_break(struct ast_compound *stmt)
{
    for (uint64_t i = 0; i < stmt->size; ++i)
        if (stmt->stmts[i]->type == AST_BREAK_STMT)
            return 1;

    return 0;
}

static void const_eval_int(struct ast_node *ast)
{
    struct ast_int *__int = ast->ast;

    switch (__int->value) {
    case 0:
        weak_compile_warn(
            ast->line_no,
            ast->col_no,
            "Loop condition will never become true."
        );
        break;
    default:
        /* Only if no break. */
        weak_compile_warn(
            ast->line_no,
            ast->col_no,
            "Loop will never ends."
        );
        break;
    }
}

static void const_eval_bin(struct ast_node *ast)
{
    struct ast_binary *bin = ast->ast;

    if (bin->lhs->type != bin->rhs->type)
        return;

    /* if (!is_const_evaluable_bin(bin))
        return; */

    enum ast_type t = bin->lhs->type;
    switch (t) {
    case AST_INT:
        break;
    case AST_FLOAT:
        /* TODO: float. */
        break;
    default:
        break;
    }
}

static void const_eval(struct ast_node *ast)
{
    enum ast_type t = ast->type;

    switch (t) {
    case AST_INT:
        const_eval_int(ast);
        break;
    case AST_BINARY:
        const_eval_bin(ast);
        break;
    /* TODO: Unary. */
    default:
        break;
    }
}

static void visit_while(struct ast_while *ast)
{
    /* Trivial case is linear scan for `break` instruction. If
       it is here, do not continue. However, this not handle case
       when `break` is nested to some other statement. */
    if (scan_break(ast->body->ast))
        return;

    const_eval(ast->cond);
}

void visit(struct ast_node *ast)
{
    assert(ast);

    switch (ast->type) {
    case AST_CHAR: /* Unused. */
    case AST_INT: /* Unused. */
    case AST_FLOAT: /* Unused. */
    case AST_STRING: /* Unused. */
    case AST_BOOL: /* Unused. */
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
        visit_compound(ast->ast);
        break;
    case AST_IF_STMT:
        break;
    case AST_FOR_STMT:
        break;
    case AST_WHILE_STMT:
        visit_while(ast->ast);
        break;
    case AST_DO_WHILE_STMT:
        break;
    case AST_RETURN_STMT:
        break;
    case AST_FUNCTION_DECL:
        visit_fn_decl(ast->ast);
        break;
    case AST_FUNCTION_CALL:
        break;
    case AST_IMPLICIT_CAST:
        break;
    default: {
        enum ast_type t = ast->type;
        weak_unreachable("Unknown AST type (%d, %s).", t, ast_type_to_string(t));
    }
    }
}

void ana_dead(struct ast_node *root)
{
    init();
    visit(root);
    ast_dump(stdout, root);
    reset();
}