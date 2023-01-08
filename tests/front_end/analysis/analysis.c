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

bool analysis_test(const char *filename)
{
    yyin = fopen(filename, "r");
    if (yyin == NULL) {
        perror("fopen()");
        return false;
    }
    yylex();
    fseek(yyin, 0, SEEK_SET);

    char   *msg = NULL;
    size_t  _ = 0;
    FILE   *msg_stream = open_memstream(&msg, &_);

    extract_assertion_comment(yyin, msg_stream);

    tok_array_t *toks = lex_consumed_tokens();

    if (!setjmp(weak_fatal_error_buf)) {
        ast_node_t *ast = parse(toks->data, toks->data + toks->count);
        analysis_variable_use_analysis(ast);
        ast_node_cleanup(ast);
    }

    lex_reset_state();
    lex_init_state();

    yylex_destroy();
    tokens_cleanup(toks);
    fclose(msg_stream);
    free(msg);

    return true;
}

int main()
{
    int ret = 0;
//    static char *err_buf = NULL;
//    static char *warn_buf = NULL;
//    static size_t err_buf_len = 0;
//    static size_t warn_buf_len = 0;

//    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
//    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

//    ASSERT_TRUE(diag_error_memstream != NULL);
//    ASSERT_TRUE(diag_warn_memstream != NULL);

    should_handle_fatal_errors = true;
    if (!do_on_each_file("/variable_use_analysis/errors", analysis_test)) {
        ret = -1;
    }

    should_handle_fatal_errors = false;
    if (!do_on_each_file("/variable_use_analysis/warns", analysis_test)) {
        ret = -1;
    }

//    if (err_buf)
//        fputs(err_buf, stderr);

//    if (warn_buf)
//        fputs(err_buf, stderr);

//    fclose(diag_error_memstream);
//    fclose(diag_warn_memstream);
//    free(err_buf);
//    free(warn_buf);
    return ret;
}