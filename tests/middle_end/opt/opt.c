/* opt.c - Test cases for optimizations.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ddg.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/opt/opt.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void (*opt_fn)(struct ir_unit *);

char current_output_dir[128];

void ddg_dump(FILE *stream, struct ir_fn_decl *decl)
{
    struct ir_node *it = decl->body;

    while (it) {
        ir_vector_t *ddgs = &it->ddg_stmts;
        fprintf(stream, "instr %2ld: depends on (", it->instr_idx);
        vector_foreach(*ddgs, i) {
            struct ir_node *stmt = vector_at(*ddgs, i);
            fprintf(stream, "%ld", stmt->instr_idx);
            if (i < ddgs->count - 1)
                fprintf(stream, ", ");
        }
        fprintf(stream, ")\n");
        it = it->next;
    }
}

void __opt_test(const char *path, const char *filename, FILE *out_stream)
{
    char    before_opt_path[256] = {0};
    char     after_opt_path[256] = {0};

    snprintf(before_opt_path, 255, "%s/%s.dot",           current_output_dir, filename);
    snprintf( after_opt_path, 255, "%s/%s_optimized.dot", current_output_dir, filename);

    FILE   *before_opt_stream = fopen(before_opt_path, "w");
    FILE   * after_opt_stream = fopen( after_opt_path, "w");

    struct ir_unit ir = gen_ir(path);
    struct ir_node *it = ir.fn_decls;

    while (it) {
        struct ir_fn_decl *decl = it->ir;
        ir_cfg_build(decl);
        ir_ddg_build(decl);

        it = it->next;
    }

    opt_fn(&ir);

    it = ir.fn_decls;

    while (it) {
        struct ir_fn_decl *decl = it->ir;

        ir_dump_cfg(after_opt_stream, decl);
        ir_dump(out_stream, decl);

        it = it->next;
    }

    fclose(before_opt_stream);
    fclose(after_opt_stream);
    ir_unit_cleanup(&ir);
}

int opt_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __opt_test);
}

int run(const char *dir)
{
    cfg_dir(dir, current_output_dir);

    return do_on_each_file(dir, opt_test);
}

int main()
{
#if 0
    opt_fn = ir_opt_fold;
    if (run("fold") < 0)
        return -1;
#endif

#if 0
    opt_fn = ir_opt_arith;
    if (run("arith") < 0)
        return -1;
#endif

#if 0
    opt_fn = ir_opt_dead_code_elimination;
    if (run("dead_code") < 0)
        return -1;
#endif

#if 0
    opt_fn = ir_opt_reorder;
    if (run("reorder") < 0)
        return -1;
#endif

#if 0
    opt_fn = ir_opt_unreachable_code;
    if (run("unreachable") < 0)
        return -1;
#endif

#if 1
    opt_fn = ir_opt_data_flow;
    if (run("data_flow") < 0)
        return -1;
#endif

    return 0;
}