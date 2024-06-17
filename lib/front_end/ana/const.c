/* const.c - Constant AST analyzer and interpreter.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/const.h"
#include "front_end/ana/ast_storage.h"
#include "front_end/ast/ast.h"
#include "util/unreachable.h"

static struct ast_storage storage;

void const_init()
{
    ast_storage_init(&storage);
}

void const_reset()
{
    ast_storage_init(&storage);
}

void const_start_scope()
{
    ast_storage_start_scope(&storage);
}

void const_end_scope()
{
    ast_storage_end_scope(&storage);
}

void const_try_store(struct ast_node *ast)
{
    if (ast->type != AST_VAR_DECL)
        return;

    struct ast_var_decl *var = ast->ast;

    if (!var->body)
        /* Parameter without body. */
        return;

    if (is_const_evaluable(var->body))
        ast_storage_push(&storage, var->name, ast);
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

    return is_const_evaluable(bin->lhs) &&
           is_const_evaluable(bin->rhs);    
}

static bool is_const_evaluable_sym(struct ast_sym *sym)
{
    return ast_storage_lookup(&storage, sym->value);
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
        return is_const_evaluable_sym(ast->ast);
    default:
        weak_unreachable("Unknown AST type (%d, %s).", t, ast_type_to_string(t));
    }
}

void const_statistics(FILE *stream)
{
    hashmap_foreach(&storage.scopes, k, v) {
        (void) k;

        struct ast_storage_decl *decl = (struct ast_storage_decl *) v;

        fprintf(stream, "const: `%s`\n", decl->name);
    }
}