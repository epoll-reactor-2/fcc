/* sema_type.c - Adding type information to the AST.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/sema/sema.h"
#include <assert.h>


static void visit(struct ast_node **ast);



/**********************************************
 **           Typed expressions              **
 **********************************************/

/**********************************************
 **          Tree traversal only             **
 **********************************************/
static void visit_compound(struct ast_node *ast)
{
    struct ast_compound *compound = ast->ast;

    for (uint64_t i = 0; i < compound->size; ++i)
        visit(&compound->stmts[i]);
}

static void visit_fn_decl(struct ast_node *ast)
{
    struct ast_fn_decl *decl = ast->ast;

    struct ast_compound *args = decl->args->ast;
    if (args && args->size > 0)
        visit(&decl->args);

    visit(&decl->body);
}

static void visit(struct ast_node **ast)
{
    assert(ast);

    switch ((*ast)->type) {
    /* Only for full tree traversal. */
    case AST_COMPOUND_STMT:
        visit_compound(*ast);
        break;
    case AST_FUNCTION_DECL:
        visit_fn_decl(*ast);
        break;
    /* Stuff. */
    case AST_ARRAY_DECL:
        break;
    case AST_FOR_RANGE_STMT:
        break;
    /* Ignore. */
    default:
        break;
    }
}

/**********************************************
 **               Driver code                **
 **********************************************/
void sema_type(struct ast_node **ast)
{
    visit(ast);
}