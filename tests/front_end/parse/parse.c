/* parse.c - Test case for parser.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

/* Parse file and compare result with expected.
   \return true on success, false on failure. */
bool parse_test(const char *path, const char *filename)
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
        ast_dump(dump_stream, ast);
        ast_node_cleanup(ast);

        get_init_comment(yyin, ast_stream, NULL);
        if (strcmp(expected, generated) != 0) {
            printf("AST's mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            ok = 0;
            goto exit;
        }
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

int main()
{
    return do_on_each_file("parser", parse_test);
}
