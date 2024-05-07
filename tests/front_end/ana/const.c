/* const.c - Test cases for constant AST evaluation.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/const.h"
#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "front_end/sema/sema.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool test(const char *program)
{
    const char *file = "/tmp/__const_test.wl";
    FILE       *mem  = fopen(file, "wr");

    if (!mem)
        weak_fatal_errno("fopen()");

    if (fputs(program, mem) < 0)
        weak_fatal_errno("fputs()");

    if (fflush(mem) < 0)
        weak_fatal_errno("fflush()");

    struct ast_node *ast = gen_ast(file);

    if (fclose(mem) < 0)
        weak_fatal_errno("fclose()");

    if (remove(file) < 0)
        weak_fatal_errno("remove()");

    struct ast_compound *tu   = ast->ast;
    struct ast_fn_decl  *decl = tu->stmts[0]->ast;
    struct ast_compound *body = decl->body->ast;
    struct ast_ret      *ret  = body->stmts[0]->ast;

    ast_dump(stdout, ret->op);

    return is_const_evaluable(ret->op);
}

bool is_const(const char *expr)
{
    char buf[8192];
    snprintf(
        buf, sizeof (buf) - 1,
        "int main() {\n"
        "    return %s;\n"
        "}",
        expr
    );

    return test(buf);
}

int main()
{
    puts("Run constant tests");
    ASSERT_TRUE (is_const("1 * 2 + 3 * 4"));
    ASSERT_FALSE(is_const("a + b"));
    ASSERT_FALSE(is_const("1 + v"));
    ASSERT_FALSE(is_const("v + 1"));
}