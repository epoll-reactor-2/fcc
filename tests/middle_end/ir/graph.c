/* graph.c - Tests for IR graph functions.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/analysis/analysis.h"
#include "front_end/ast/ast.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/gen.h"
#include "middle_end/ir/graph.h"
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

bool ir_test(const char *path, const char *filename)
{
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
    char    cfg_path[256] = {0};
    char    dom_tree_path[256] = {0};

    snprintf(cfg_path, 255, "%s/%s_cfg.dot", current_output_dir, filename);
    snprintf(dom_tree_path, 255, "%s/%s_dom_tree.dot", current_output_dir, filename);

    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);
    FILE   *cfg_stream       = fopen(cfg_path, "w");
    FILE   *dom_tree_stream  = fopen(dom_tree_path, "w");

    if (expected_stream == NULL) {
        perror("open_memstream()");
        return false;
    }

    if (!cfg_stream || !dom_tree_stream) {
        perror("fopen()");
        abort();
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

        ir_compute_dom_tree(it);
        ir_compute_dom_frontier(it);
        ir_compute_ssa(it);

        while (it) {
            ir_dump_cfg(cfg_stream, it->ir);
            ir_dump_dom_tree(dom_tree_stream, it->ir);
            fflush(cfg_stream);
            fflush(dom_tree_stream);
            it = it->next;
        }

        ast_node_cleanup(ast);
        ir_unit_cleanup(ir);

        printf("Success!\n");
    } else {
        /// Error, will be printed in main.
        success = false;
    }

    yylex_destroy();
    tokens_cleanup(toks);
    fclose(expected_stream);
    fclose(generated_stream);
    fclose(cfg_stream);
    fclose(dom_tree_stream);
    free(expected);
    free(generated);

    return success;
}

static char *err_buf = NULL;
static char *warn_buf = NULL;
static size_t err_buf_len = 0;
static size_t warn_buf_len = 0;

int run(const char *dir)
{
    int  ret       =  0;
    char path[256] = {0};
    snprintf(path, sizeof (path) - 1, "/test_inputs/%s", dir);

    cfg_dir(dir);

    if (!do_on_each_file(path, ir_test)) {
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

    if (run("ir_graph") < 0)
        return -1;

    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    free(err_buf);
    free(warn_buf);
    return 0;
}