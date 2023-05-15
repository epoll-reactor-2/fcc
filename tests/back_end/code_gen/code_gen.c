/* ast_storage.с - Test case for code generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/code_gen.h"
#include "front_end/analysis/analysis.h"
#include "front_end/ast/ast.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "utility/diagnostic.h"
#include "utils/test_utils.h"

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool code_gen_test(const char *filename)
{
    lex_reset_state();
    lex_init_state();

    if (!yyin) yyin = fopen(filename, "r");
    else yyin = freopen(filename, "r", yyin);
    if (yyin == NULL) {
        perror("fopen()");
        return false;
    }
    yylex();
    fseek(yyin, 0, SEEK_SET);

    tok_array_t *toks = lex_consumed_tokens();

    if (!setjmp(weak_fatal_error_buf)) {
        printf("\n");
        ast_node_t *ast = parse(toks->data, toks->data + toks->count);
        analysis_variable_use_analysis(ast);
        analysis_functions_analysis(ast);
        analysis_type_analysis(ast);
        code_gen(ast);

        system("cat /tmp/__code_dump.s");
        system("as /tmp/__code_dump.s -o /tmp/__code_dump.o");
        system("ld /tmp/__code_dump.o -o /tmp/__code_dump");
        system("strip --remove-section=.note.gnu.property /tmp/__code_dump");
        system("strace /tmp/__code_dump");
    } else {
        /// Error, will be printed in main.
        return false;
    }

    yylex_destroy();
    tokens_cleanup(toks);

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

    if (!do_on_each_file("/test_inputs/code_generator", code_gen_test)) {
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