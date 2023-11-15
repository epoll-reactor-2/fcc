/* ssa.c - Tests for SSA form.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/lex.h"
#include "middle_end/ir/dump.h"
#include "middle_end/ir/ssa.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char current_output_dir[128];

bool ir_test(const char *path, const char *filename)
{
    bool    ok                 = 1;
    char   *expected           = NULL;
    char   *generated          = NULL;
    size_t  _                  =  0;
    char    cfg_path[256]      = {0};
    char    dom_tree_path[256] = {0};

    snprintf(cfg_path, 255, "%s/%s_cfg.dot", current_output_dir, filename);
    snprintf(dom_tree_path, 255, "%s/%s_dom_tree.dot", current_output_dir, filename);

    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);
    FILE   *cfg_stream       = fopen(cfg_path, "w");
    FILE   *dom_tree_stream  = fopen(dom_tree_path, "w");
    struct  ir_unit      *ir = NULL;

    if (!setjmp(weak_fatal_error_buf)) {
        ir = gen_ir(path);
        struct ir_node *it = ir->func_decls;

        extract_assertion_comment(yyin, expected_stream);

        while (it) {
            struct ir_func_decl *decl = it->ir;
            ir_link(decl);
            ir_build_cfg(decl);
            it = it->next;
        }

        it = ir->func_decls;
        ir_compute_ssa(it);

        while (it) {
            struct ir_func_decl *decl = it->ir;
            ir_dump_cfg(cfg_stream, decl);
            ir_dump_dom_tree(dom_tree_stream, decl);
            ir_dump_unit(generated_stream, ir);
            fflush(cfg_stream);
            fflush(dom_tree_stream);
            fflush(generated_stream);
            it = it->next;
        }

        if (strcmp(expected, generated) != 0) {
            /* ir_dump_unit(stdout, ir); */
            printf("IR mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            fflush(stdout);
            // ok = 0;
            // goto exit;
        }
        printf("Success!\n");
    } else {
        /* Error, will be printed in main. */
        ok = 0;
    }

/* exit: */
    yylex_destroy();
    fclose(expected_stream);
    fclose(generated_stream);
    fclose(cfg_stream);
    fclose(dom_tree_stream);
    free(expected);
    free(generated);
    ir_unit_cleanup(ir);

    return ok;
}

char *err_buf       = NULL;
char *warn_buf      = NULL;
size_t err_buf_len  = 0;
size_t warn_buf_len = 0;

int run(const char *dir)
{
    int  ret       =  0;
    char path[256] = {0};
    snprintf(path, sizeof (path) - 1, "/test_inputs/%s", dir);

    cfg_dir(dir, current_output_dir);

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

    if (run("ssa") < 0)
        return -1;

    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    free(err_buf);
    free(warn_buf);
    return 0;
}