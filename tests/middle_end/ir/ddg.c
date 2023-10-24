/* ddg.c - Test case for data dependence graph.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/ast/ast.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ddg.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/gen.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>
#include <sys/stat.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char current_output_dir[128];

void create_dir(const char *name)
{
    struct stat st = {0};
    if (stat(name, &st) == -1) {
        if (mkdir(name, 0777) < 0) {
            perror("mkdir()");
            abort();
        }
    }
}

void cfg_dir(const char *name)
{
    snprintf(current_output_dir, 127, "test_outputs/%s", name);

    create_dir("test_outputs");
    create_dir(current_output_dir);
}

void ddg_dump(FILE *stream, struct ir_func_decl *decl)
{
    struct ir_node *it = decl->body;

    while (it) {
        ir_vector_t *ddgs = &it->ddg_stmts;
        fprintf(stream, "instr %2d: depends on (", it->instr_idx);
        vector_foreach(*ddgs, i) {
            struct ir_node *stmt = vector_at(*ddgs, i);
            fprintf(stream, "%d", stmt->instr_idx);
            if (i < ddgs->count - 1)
                fprintf(stream, ", ");
        }
        fprintf(stream, ")\n");
        it = it->next;
    }
}

bool ir_test(const char *path, const char *filename)
{
    (void) filename;

    lex_reset_state();
    lex_init_state();

    if (!yyin) yyin = fopen(path, "r");
    else yyin = freopen(path, "r", yyin);
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

    FILE   * expected_stream = open_memstream(&expected, &_);
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

        struct ir_unit *ir = ir_gen(ast);
        struct ir_node *it = ir->func_decls;

        while (it) {
            ir_ddg_build(it->ir);
            ir_dump(generated_stream, it->ir);
            fprintf(generated_stream, "--------\n");
            ddg_dump(generated_stream, it->ir);
            it = it->next;
        }

        fflush(generated_stream);
        ast_node_cleanup(ast);
        ir_unit_cleanup(ir);

        if (strcmp(expected, generated) != 0) {
            printf("IR mismatch:\n%s\ngenerated\n%s\nexpected\n", generated, expected);
            success = false;
            goto exit;
        }
        printf("Success!\n");
    } else {
        /// Error, will be printed in main.
        success = false;
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

static char *err_buf = NULL;
static char *warn_buf = NULL;
static size_t err_buf_len = 0;
static size_t warn_buf_len = 0;

int run()
{
    int ret = 0;

    cfg_dir("ddg");

    if (!do_on_each_file("/test_inputs/ddg", ir_test)) {
        ret = -1;

        if (err_buf)
            fputs(err_buf, stderr);

        if (warn_buf)
            fputs(warn_buf, stderr);
    }

    return ret;
}

int main()
{
    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    int ret = run();

    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    free(err_buf);
    free(warn_buf);
    return ret;
}