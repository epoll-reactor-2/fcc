/* code_gen.с - Test case for code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/code_gen.h"
#include "front_end/analysis/analysis.h"
#include "front_end/ast/ast_node.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "utility/diagnostic.h"
    #include "utils/test_utils.h"
#include <string.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool code_gen_test(const char *filename)
{
    lex_reset_state();
    lex_init_state();

    bool success = true;

    if (!yyin) yyin = fopen(filename, "r");
    else yyin = freopen(filename, "r", yyin);
    if (yyin == NULL) {
        perror("fopen()");
        return false;
    }
    yylex();
    fseek(yyin, 0, SEEK_SET);

    tok_array_t *toks = lex_consumed_tokens();

    char *expected = NULL;
    size_t _;
    FILE *stream = open_memstream(&expected, &_);
    extract_assertion_comment(yyin, stream);

    int expected_exit_code = 0;
    sscanf(expected, "%d", &expected_exit_code);
    fclose(stream);

    ast_node_t *ast = NULL;

    if (!setjmp(weak_fatal_error_buf)) {
        /// No compilation errors, all fine.
        printf("\n");
        ast = parse(toks->data, toks->data + toks->count);
        analysis_variable_use_analysis(ast);
        analysis_functions_analysis(ast);
        analysis_type_analysis(ast);
        code_gen(ast);

        system(
            "cat /tmp/__code_dump.s && "
            "as /tmp/__code_dump.s -o /tmp/__code_dump.o && "
            "ld /tmp/__code_dump.o -o /tmp/__code_dump && "
            "strip --remove-section=.note.gnu.property /tmp/__code_dump"
        );
        int ret = system("/tmp/__code_dump");
        /// \todo: What if we will test Unix signals too?
        ///        Then other test function with signal handling can be
        ///        implemented, I guess.
        if (WIFSIGNALED(ret)) {
            printf("Unexpected signal received: %s\n", strsignal(WTERMSIG(ret)));
            success = false;
            goto exit;
        }
        int exit_code = WEXITSTATUS(ret);
        if (exit_code != expected_exit_code) {
            printf("Exit codes mismatch: got %d, expected %d\n", exit_code, expected_exit_code);
            success = false;
            goto exit;
        }
        printf("Success!\n");
    } else {
        /// Compilation error; will be displayed in main().
        success = false;
        goto exit;
    }

exit:
    yylex_destroy();
    tokens_cleanup(toks);
    ast_node_cleanup(ast);

    return success;
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

    if (!do_on_each_file("/test_inputs/code_generator", code_gen_test)) {
        ret = -1;

        if (err_buf)
            fputs(err_buf, stderr);

        if (warn_buf)
            fputs(warn_buf, stderr);
    }

    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    return ret;
}
