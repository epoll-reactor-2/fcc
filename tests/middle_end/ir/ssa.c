/* ssa.c - Tests for SSA form.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/ssa.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char current_output_dir[128];

void __ssa_test(const char *path, const char *filename, FILE *out_stream)
{
    char    dom_path[256]      = {0};
    char    cfg_path[256]      = {0};

    snprintf(dom_path, 255, "%s/%s_dom_tree.dot", current_output_dir, filename);
    snprintf(cfg_path, 255, "%s/%s_cfg.dot",      current_output_dir, filename);

    FILE   *dom_stream         = fopen(dom_path, "w");
    FILE   *cfg_stream         = fopen(cfg_path, "w");

    struct ir_unit  ir = gen_ir(path);
    struct ir_node *it = ir.fn_decls;

    while (it) {
        struct ir_fn_decl *decl = it->ir;
        ir_cfg_build(decl);
        it = it->next;
    }

    it = ir.fn_decls;
    ir_compute_ssa(it);

    while (it) {
        struct ir_fn_decl *decl = it->ir;
        ir_dump_cfg(cfg_stream, decl);
        ir_dump_dom_tree(dom_stream, decl);
        ir_dump_unit(out_stream, &ir);
        fflush(cfg_stream);
        fflush(dom_stream);
        fflush(out_stream);
        it = it->next;
    }

    ir_unit_cleanup(&ir);
    fclose(cfg_stream);
    fclose(dom_stream);
}

int ssa_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __ssa_test);
}

int main()
{
    cfg_dir("ssa", current_output_dir);
    do_on_each_file("ssa", ssa_test);
    return 0;
}