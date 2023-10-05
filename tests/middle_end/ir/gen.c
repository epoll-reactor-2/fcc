/* gen.c - Tests for IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/ast/ast.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/gen.h"
#include "middle_end/ir/dump.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

bool ir_test(const char *filename)
{
    if (strstr(filename, "disabled_") != NULL)
        return 1;

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

    bool    success = true;
    char   *expected = NULL;
    char   *generated = NULL;
    size_t  _ = 0;
    FILE   *expected_stream = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);

    if (expected_stream == NULL) {
        perror("open_memstream()");
        return false;
    }

    extract_assertion_comment(yyin, expected_stream);

    if (!setjmp(weak_fatal_error_buf)) {
        struct ast_node *ast = parse(toks->data, toks->data + toks->count);

        /// Preconditions for IR generator.
        analysis_variable_use_analysis(ast);
        analysis_functions_analysis(ast);
        analysis_type_analysis(ast);

        struct ir_node *ir = ir_gen(ast);
        struct ir_node *it = ir;

        while (it) {
            ir_dump(generated_stream, it->ir);
            it = it->next;
        }
        // for (uint64_t i = 0; i < ir.decls_size; ++i) {
            // ir_dump(generated_stream, ir.decls[i].ir);
// 
            // struct ir_func_decl *decl = ir.decls[0].ir;
            // ir_dump_graph_dot(stdout, decl);
        // }

        fflush(generated_stream);
        ast_node_cleanup(ast);
        ir_node_cleanup(ir);
        
        if (strcmp(expected, generated) != 0) {
            printf("IR mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            // success = false;
            goto exit;
        }
        printf("Success!\n");
    } else {
        /// Error, will be printed in main.
        return false;
    }

exit:
    yylex_destroy();
    tokens_cleanup(toks);
    fclose(expected_stream);
    fclose(generated_stream);
    free(expected);
    free(generated);

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

    if (!do_on_each_file("/test_inputs/ir_gen", ir_test)) {
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