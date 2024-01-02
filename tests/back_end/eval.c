/* fold.c - Test cases for IR interpreter.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/eval.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/type.h"
#include "middle_end/opt/opt.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void cfg_edge_vector_dump(FILE *stream, ir_vector_t *v)
{
    vector_foreach(*v, i) {
        struct ir_node *p = vector_at(*v, i);
        fprintf(stream, "%ld", p->instr_idx);
        if (i < v->count - 1)
            fprintf(stream, ", ");
    }
}

void cfg_edges_dump(FILE *stream, struct ir_fn_decl *decl)
{
    struct ir_node *it = decl->body;

    while (it) {
        fprintf(stream, "% 3ld: cfg = %ld", it->instr_idx, it->cfg_block_no);

        if (it->cfg.preds.count > 0) {
            fprintf(stream, ", prev = (");
            cfg_edge_vector_dump(stream, &it->cfg.preds);
            fprintf(stream, ")");
        }
        if (it->cfg.succs.count > 0) {
            fprintf(stream, ", next = (");
            cfg_edge_vector_dump(stream, &it->cfg.succs);
            fprintf(stream, ")");
        }

        fputc('\n', stream);
        it = it->next;
    }
}

bool ir_test(const char *path, const char *filename)
{
    (void) filename;

    bool    ok               = 1;
    char   *expected         = NULL;
    char   *generated        = NULL;
    size_t  _                = 0;
    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);
    FILE   *tmp_cfg          = fopen("/tmp/g.dot", "w+");
    struct  ir_unit    *unit = NULL;
    struct  ir_node    *it   = NULL;

    if (!setjmp(weak_fatal_error_buf)) {
        unit = gen_ir(path);
        ir_type_pass(unit);

        extract_assertion_comment(yyin, expected_stream);

        /* ir_dump_unit(stdout, ir); */

        it = unit->fn_decls;
        while (it) {
            struct ir_fn_decl *decl = it->ir;
            /* Reordering before building CFG links. */
            ir_opt_reorder(decl);
            ir_opt_arith(decl);

            ir_cfg_build(decl);

            /* ir_dump(stdout, decl); */

            /* Wrong
               ir_opt_unreachable_code(decl); */

            /* There is some trouble with
               data flow of input function
               parameters.

               ir_opt_data_flow(decl); */

            /* ir_dump_cfg(tmp_cfg, decl); */
            /* ir_dump(stdout, decl); */
            /* cfg_edges_dump(stdout, decl); */
            fflush(tmp_cfg);
            it = it->next;
        }

        int32_t exit_code = eval(unit);
        int32_t expected_code = 0;

        fscanf(expected_stream, "%d", &expected_code);

        if (exit_code != expected_code) {
            /* ir_dump_unit(stdout, ir); */
            printf("Return value mismatch: got %d, expected %d\n", exit_code, expected_code);
            ok = 0;
            goto exit;
        }
        puts("Success!");
    } else {
        /// Error, will be printed in main.
        return 0;
    }

exit:
    yylex_destroy();
    fclose(expected_stream);
    fclose(generated_stream);
    free(expected);
    free(generated);
    ir_unit_cleanup(unit);

    return ok;
}

int main()
{
    int     ret          = 0;
    char   *err_buf      = NULL;
    char   *warn_buf     = NULL;
    size_t  err_buf_len  = 0;
    size_t  warn_buf_len = 0;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    if (!do_on_each_file("/test_inputs/eval", ir_test)) {
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