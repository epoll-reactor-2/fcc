/* const.c - Test cases for constant AST evaluation.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/anal/const.h"
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

    /* NOTE, TODO: Hard-coded test. Decide, how to use
                   it along with AST DCE. Decide, how to
                   write unit test for this. */
    struct ast_compound *tu   = ast->ast;
    struct ast_fn_decl  *decl = tu->stmts[0]->ast;
    struct ast_compound *body = decl->body->ast;
    struct ast_node     *var1 = body->stmts[0];
    struct ast_node     *var2 = body->stmts[1];
    struct ast_node     *var3 = body->stmts[2];
    struct ast_node     *var4 = body->stmts[3];
    struct ast_ret      *ret  = body->stmts[4]->ast;

    ASSERT_TRUE(var1);
    ASSERT_TRUE(var2);
    ASSERT_TRUE(var3);
    ASSERT_TRUE(var4);
    ASSERT_TRUE(ret);

    const_init();
    const_try_store(var1);
    const_try_store(var2);
    const_try_store(var3);
    const_try_store(var4);

    const_statistics(stdout);
    const_reset();

    return 1;
}

bool is_const(const char *expr)
{
    char buf[8192];
    snprintf(
        buf, sizeof (buf) - 1,
        "int main(int arg) {\n"
        "    int val1 = %s;\n"
        "    int val2 = arg;\n"
        "    int val3 = %s + val1;\n"
        "    int val4 = 1 + val2;\n"
        "    return val1;\n"
        "}",
        expr, expr
    );

    return test(buf);
}

int main()
{
    puts("Run constant tests");
    return 0;
    // return is_const("1 * 2 + 3 * 4");
}