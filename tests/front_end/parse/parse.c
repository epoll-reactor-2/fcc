/* parse.c - Test case for parser.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "utility/diagnostic.h"
#include "utils/test_utils.h"
#include <dirent.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

/// Parse file and compare result with expected.
///
/// \return true on success, false on failure.
bool parse_test(const char *filename)
{
    lex_reset_state();
    lex_init_state();

    yyin = fopen(filename, "r");
    if (yyin == NULL) {
        perror("fopen()");
        return false;
    }
    yylex();
    fseek(yyin, 0, SEEK_SET);

    char   *expected = NULL;
    char   *generated = NULL;
    size_t  _ = 0;
    FILE   *ast_stream = open_memstream(&expected, &_);
    FILE   *dump_stream = open_memstream(&generated, &_);

    extract_assertion_comment(yyin, ast_stream);

    tok_array_t *toks = lex_consumed_tokens();
    fclose(yyin);

    if (!setjmp(weak_fatal_error_buf)) {
        ast_node_t *ast = parse(toks->data, toks->data + toks->count);
        ast_dump(dump_stream, ast);
        ast_node_cleanup(ast);

        if (strcmp(expected, generated) != 0) {
            printf("AST's mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            return false;
        }
        printf("Success!\n");
        fflush(stdout);
    } else {
        /// Error, will be printed in main.
        return false;
    }

    yylex_destroy();
    tokens_cleanup(toks);
    fclose(ast_stream);
    fclose(dump_stream);
    free(expected);
    free(generated);

    return true;
}

int main()
{
    int ret = 0;
    static char *err_buf = NULL;
    static char *warn_buf = NULL;
    static size_t err_buf_len = 0;
    static size_t warn_buf_len = 0;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    ASSERT_TRUE(diag_error_memstream != NULL);
    ASSERT_TRUE(diag_warn_memstream != NULL);

    if (!do_on_each_file("/parser", parse_test)) {
        ret = -1;

        if (err_buf)
            fputs(err_buf, stderr);

        if (warn_buf)
            fputs(warn_buf, stderr);
    }

    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    free(err_buf);
    free(warn_buf);
    return ret;
}