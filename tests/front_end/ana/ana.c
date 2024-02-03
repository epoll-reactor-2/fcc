/* analysis.c - Test cases for all analyzers.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/ana.h"
#include "front_end/ast/ast.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool ignore_warns = false;

void(*analysis_fn)(struct ast_node *) = NULL;

char   *err_buf      = NULL;
char   *warn_buf     = NULL;
size_t  err_buf_len  = 0;
size_t  warn_buf_len = 0;

bool analysis_test(const char *path, const char *filename)
{
    (void) filename;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    /// Static due to the `longjmp()` semantics [-Werror=clobbered].
    static bool ok      = 1;
    char   *msg         = NULL;
    size_t  _           = 0;
    FILE   *msg_stream  = open_memstream(&msg, &_);

    tok_array_t *tokens = gen_tokens(path);

    extract_compiler_messages(path, yyin, msg_stream);

    struct ast_node *ast = parse(tokens->data, tokens->data + tokens->count);

    if (!setjmp(weak_fatal_error_buf)) {
        analysis_fn(ast);
        /// Normal code.
        if (!ignore_warns) {
            if (strcmp(warn_buf, msg) == 0) {
                printf("Success!\n");
            } else {
                printf("generated warning:\n%s", warn_buf);
                printf("expected warning:\n%s", msg);
                ok = false;
                goto exit;
            }
        }
    } else {
        /* Code with fatal errors. */
        if (strcmp(err_buf, msg) == 0) {
            printf("Success!\n");
        } else {
            printf("generated error:\n%s", err_buf);
            printf("expected error:\n%s", msg);
            ok = false;
            goto exit;
        }
    }

    if (ignore_warns && !err_buf) {
        fprintf(stderr, "Expected compile error\n");
        ok = false;
    }

exit:
    ast_node_cleanup(ast);
    tokens_cleanup(tokens);
    yylex_destroy();
    fclose(msg_stream);
    free(msg);
    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    free(err_buf);
    free(warn_buf);

    return ok;
}

int main()
{
    analysis_fn = analysis_functions_analysis;
    ignore_warns = 1;
    if (!do_on_each_file("/test_inputs/fn_ana", analysis_test))
        return -1;

    analysis_fn = analysis_variable_use_analysis;
    ignore_warns = 1;
    if (!do_on_each_file("/test_inputs/var_ana/errors", analysis_test))
        return -1;

    analysis_fn = analysis_variable_use_analysis;
    ignore_warns = 0;
    if (!do_on_each_file("/test_inputs/var_ana/warns", analysis_test))
        return -1;

    analysis_fn = analysis_type_analysis;
    ignore_warns = 1;
    if (!do_on_each_file("/test_inputs/type_ana", analysis_test))
        return -1;

    return 0;
}
