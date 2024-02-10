/* cfg.c - Tests for CFG edges.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir_dump.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char current_output_dir[128];

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

int cfg_test(const char *path, const char *filename)
{
    (void) filename;

    int     rc               = 0;
    char   *expected         = NULL;
    char   *generated        = NULL;
    size_t  _                = 0;
    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);
    char    cfg_path[256]    = {0};

    snprintf(cfg_path, 255, "%s/%s_cfg.dot", current_output_dir, filename);

    FILE   *cfg_stream       = fopen(cfg_path, "w");

    if (!setjmp(weak_fatal_error_buf)) {
        struct ir_unit  ir = gen_ir(path);
        struct ir_node *it = ir.fn_decls;

        get_init_comment(yyin, expected_stream, NULL);

        while (it) {
            struct ir_fn_decl *decl = it->ir;
            ir_cfg_build(decl);

            ir_dump(generated_stream, decl);
            ir_dump_cfg(cfg_stream, decl);
            fprintf(generated_stream, "--------\n");
            cfg_edges_dump(generated_stream, decl);
            it = it->next;
        }

        fflush(generated_stream);
        ir_unit_cleanup(&ir);
    
        if (strcmp(expected, generated) != 0) {
            printf("IR mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            rc = -1;
            goto exit;
        }
    } else {
        /* Error, will be printed in main. */
        return -1;
    }

exit:
    fclose(yyin);
    yylex_destroy();
    fclose(expected_stream);
    fclose(generated_stream);
    fclose(cfg_stream);
    free(expected);
    free(generated);

    return rc;
}

int main()
{
    cfg_dir("cfg", current_output_dir);

    return do_on_each_file("cfg", cfg_test);
}