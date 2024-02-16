/* cfg.c - Tests for CFG edges.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir_dump.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"

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

void __cfg_test(const char *path, const char *filename, FILE *out_stream)
{
    char  cfg_path[256] = {0};
    FILE *cfg_stream    = NULL;

    snprintf(cfg_path, 255, "%s/%s_cfg.dot", current_output_dir, filename);

    cfg_stream = fopen(cfg_path, "w");

    struct ir_unit ir = gen_ir(path);
    struct ir_node *it = ir.fn_decls;

    while (it) {
        struct ir_fn_decl *decl = it->ir;
        ir_cfg_build(decl);

        ir_dump(out_stream, decl);
        ir_dump_cfg(cfg_stream, decl);
        fprintf(out_stream, "--------\n");
        cfg_edges_dump(out_stream, decl);
        it = it->next;
    }

    ir_unit_cleanup(&ir);
    fclose(cfg_stream);
}

int cfg_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __cfg_test);
}

int main()
{
    cfg_dir("cfg", current_output_dir);

    return do_on_each_file("cfg", cfg_test);
}