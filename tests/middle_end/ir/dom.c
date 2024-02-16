/* dom.c - Tests for dominator tree.
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

void idom_dump(FILE *stream, struct ir_fn_decl *decl)
{
    struct ir_node *it = decl->body;

    while (it) {
        if (it->idom)
            fprintf(
                stream, "idom(%ld) = %ld\n",
                it->instr_idx,
                it->idom->instr_idx
            );

        it = it->next;
    }
}

void __dom_test(const char *path, const char *filename, FILE *out_stream)
{
    (void) filename;

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
        ir_dominator_tree(decl);
        ir_dominance_frontier(decl);
        ir_dump_dom_tree(dom_stream, decl);
        ir_dump_cfg(cfg_stream, decl);
        ir_dump(out_stream, decl);
        fprintf(out_stream, "--------\n");
        idom_dump(out_stream, decl);
        it = it->next;
    }

    ir_unit_cleanup(&ir);
    fclose(cfg_stream);
    fclose(dom_stream);
}

int dom_test(const char *path, const char *filename)
{
    (void) filename;

    return compare_with_comment(path, filename, __dom_test);
}

int main()
{
    cfg_dir("dom", current_output_dir);

    return do_on_each_file("dom", dom_test);
}