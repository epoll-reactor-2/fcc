/* sema.c - Test cases for semantic AST passes.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "front_end/sema/sema.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void (*sema_fn)(struct ast_node **);

/* Parse file and compare result with expected.
   \return 1 on success, 0 on failure. */
bool sema_test(const char *path, const char *filename)
{
    (void) filename;

    bool    ok          = 1;
    char   *expected    = NULL;
    char   *generated   = NULL;
    size_t  _           = 0;
    FILE   *ast_stream  = open_memstream(&expected, &_);
    FILE   *dump_stream = open_memstream(&generated, &_);

    if (!setjmp(weak_fatal_error_buf)) {
        struct ast_node *ast = gen_ast(path);
        sema_fn(&ast);
        ast_dump_omit_pos(dump_stream, ast);
        ast_node_cleanup(ast);

        get_init_comment(yyin, ast_stream, NULL);
        if (strcmp(expected, generated) != 0) {
            printf("AST's mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            ok = 0;
            goto exit;
        }
        printf("Success!\n");
    } else {
        /* Error, will be printed in main. */
        ok = 0;
    }

exit:
    fclose(yyin);
    yylex_destroy();
    fclose(ast_stream);
    fclose(dump_stream);
    free(expected);
    free(generated);

    return ok;
}

int run(const char *dir)
{
    return do_on_each_file(dir, sema_test);
}

int main()
{
    sema_fn = sema_lower;
    if (run("sema_lower") < 0)
        return -1;

    sema_fn = sema_type;
    if (run("sema_type") < 0)
        return -1;

    return 0;
}