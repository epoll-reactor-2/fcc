/* const.c - Constant AST analyzer and interpreter.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/const.h"
#include "front_end/ast/ast.h"
#include "util/unreachable.h"

/* TODO: Const symbols mapping. */

void const_init()
{}

void const_reset()
{}

void const_try_store(struct ast_var_decl *decl)
{
    if (is_const_evaluable(decl->body))
        /* Add. */{}
}

static bool numeric(enum ast_type t)
{
    switch (t) {
    case AST_BOOL:
    case AST_CHAR:
    case AST_INT:
    case AST_FLOAT:
        return 1;
    default:
        return 0;
    }
}

static bool is_const_evaluable_bin(struct ast_binary *bin)
{
    if (numeric(bin->lhs->type) &&
        numeric(bin->rhs->type))
        return 1;

    if ((bin->lhs->type != AST_BINARY && !numeric(bin->lhs->type)) ||
        (bin->rhs->type != AST_BINARY && !numeric(bin->rhs->type)))
        return 0;

    return is_const_evaluable(bin->lhs) &&
           is_const_evaluable(bin->rhs);    
}

bool is_const_evaluable(struct ast_node *ast)
{
    enum ast_type t = ast->type;
    switch (t) {
    case AST_BOOL:
    case AST_CHAR:
    case AST_INT:
    case AST_FLOAT:
        return 1;
    case AST_BINARY:
        return is_const_evaluable_bin(ast->ast);
    case AST_SYMBOL:
        /* TODO: Map symbols to its const property. */
        return 0;
    default:
        weak_unreachable("Unknown AST type (%d, %s).", t, ast_type_to_string(t));
    }
}