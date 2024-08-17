/* regalloc.c - Test cases for regalloc.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/regalloc.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void dump_reg_alloc(FILE *out_stream, struct ir_node *decls)
{
    struct ir_node *it = decls;

    while (it) {
        struct ir_fn_decl *decl = it->ir;

        struct ir_node *body = decl->body;

        while (body) {
            if (body->claimed_reg != IR_NO_CLAIMED_REG) {
                assert(body->type == IR_STORE);
                struct ir_store *store = body->ir;
                struct ir_sym   *sym   = store->idx->ir;

                fprintf(out_stream, "symbol % 2ld : reg %d\n", sym->idx, body->claimed_reg);
            }

            body = body->next;
        }

        it = it->next;
    }
}

void __gen_test(const char *path, unused const char *filename, FILE *out_stream)
{
    struct ir_unit ir = gen_ir(path);
    ir_reg_alloc(ir.fn_decls);
    ir_dump_unit(out_stream, &ir);
    fprintf(out_stream, "--------\n");
    dump_reg_alloc(out_stream, ir.fn_decls);
    ir_unit_cleanup(&ir);
}

int reg_alloc_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __gen_test);
}

int main()
{
    return do_on_each_file("regalloc", reg_alloc_test);
}