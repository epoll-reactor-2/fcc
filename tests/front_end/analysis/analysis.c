/* analysis.c - Test cases for all analyzers.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/ast/ast_node.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "utility/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool should_handle_fatal_errors = false;

void(*analysis_fn)(ast_node_t *) = NULL;

bool analysis_test(const char *filename)
{
    bool success = true;
    char *err_buf = NULL;
    char *warn_buf = NULL;
    size_t err_buf_len = 0;
    size_t warn_buf_len = 0;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    lex_reset_state();
    lex_init_state();

    yyin = fopen(filename, "r");
    if (yyin == NULL) {
        perror("fopen()");
        return false;
    }
    yylex();

    char   *msg = NULL;
    size_t  _ = 0;
    FILE   *msg_stream = open_memstream(&msg, &_);

    fseek(yyin, 0, SEEK_SET);
    extract_assertion_comment(yyin, msg_stream);

    tok_array_t *toks = lex_consumed_tokens();
    ast_node_t *ast = parse(toks->data, toks->data + toks->count);

    if (!setjmp(weak_fatal_error_buf)) {
        analysis_fn(ast);
        printf("generated:\n%s", warn_buf);
        printf("expected:\n%s", msg);
        if (strcmp(warn_buf, msg) == 0) {
            printf("Success!\n");
            fflush(stdout);
        } else {
            success = false;
            goto exit;
        }
    } else {
        printf("generated:\n%s", err_buf);
        printf("expected:\n%s", msg);
        if (strcmp(err_buf, msg) == 0) {
            printf("Success!\n");
            fflush(stdout);
        } else {
            success = false;
            goto exit;
        }
    }

exit:
    ast_node_cleanup(ast);
    yylex_destroy();

    return success;
}

int main()
{
    int ret = 0;

    analysis_fn = analysis_functions_analysis;
    should_handle_fatal_errors = true;
    if (!do_on_each_file("/function_analysis", analysis_test)) {
        ret = -1;
        goto exit;
    }

    analysis_fn = analysis_variable_use_analysis;
    should_handle_fatal_errors = true;
    if (!do_on_each_file("/variable_use_analysis/errors", analysis_test)) {
        ret = -1;
        goto exit;
    }

    analysis_fn = analysis_variable_use_analysis;
    should_handle_fatal_errors = false;
    if (!do_on_each_file("/variable_use_analysis/warns", analysis_test)) {
        ret = -1;
    }

exit:
    return ret;
}