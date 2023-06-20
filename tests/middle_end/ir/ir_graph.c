/* ir_graph.c - Tests for IR graph build functions.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/analysis/analysis.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir_gen.h"
#include "middle_end/ir_dump.h"
#include "middle_end/ir_graph.h"
#include "middle_end/ir.h"
#include "utils/test_utils.h"
#include <stdio.h>
#include <math.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void graph_print(bool *mat, size_t row_size)
{
    printf("\nGenerated graph\n\n       ");
    for (size_t i = 0; i < row_size; ++i)
        printf("% 3ld", i);
    printf("\n\n");
    
    for (size_t i = 0; i < row_size; ++i) {
        printf("% 3ld   [ ", i);
        for (size_t j = 0; j < row_size; ++j) {
            printf("% 2d ", mat[i * row_size + j]);
        }
        printf("]\n");
    }
    printf("\n");
}

bool ir_graph_test(const char *filename)
{
    lex_reset_state();
    lex_init_state();
    ir_reset_internal_state();

    weak_set_source_filename(filename);

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

        struct ir ir = ir_gen(ast);
        struct ir_graph graph = ir_graph_init(&ir);

        puts("\n\nGenerated IR\n");

        for (uint64_t i = 0; i < ir.decls_size; ++i)
            ir_dump(stdout, ir.decls[i].ir);

        struct ir_func_decl *func = (struct ir_func_decl *) ir.decls[0].ir;

        graph_print(graph.adj_matrix, func->body_size);

        ast_node_cleanup(ast);
        ir_cleanup(&ir);
        ir_graph_cleanup(&graph);

        printf("Success!\n\n");
        fflush(stdout);
    } else {
        /// Error, will be printed in main.
        return false;
    }

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

    if (!do_on_each_file("/test_inputs/ir_graph", ir_graph_test)) {
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