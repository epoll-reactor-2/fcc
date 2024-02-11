/* ddg.c - Test case for data dependence graph.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/lex.h"
#include "middle_end/ir/ddg.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/ir.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

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

void __ddg_test(const char *path, const char *filename, FILE *out_stream)
{
    (void) filename;

    struct ir_unit  ir = gen_ir(path);
    struct ir_node *it = ir.fn_decls;

    while (it) {
        struct ir_fn_decl *decl = it->ir;

        ir_ddg_build(decl);
        ir_cfg_build(decl);
        ir_dump(out_stream, decl);
        fprintf(out_stream, "--------\n");
        ddg_dump(out_stream, decl);
        it = it->next;
    }

    ir_unit_cleanup(&ir);
}

int ddg_test(const char *path, const char *filename)
{
    (void) filename;

    return compare_with_comment(path, filename, __ddg_test);
}

int main()
{
    return do_on_each_file("ddg", ddg_test);
}