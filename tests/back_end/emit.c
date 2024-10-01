/* gen.c - Tests for code generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_dump.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/opt/opt.h"
#include "back_end/emit.h"
#include "back_end/back_end.h"
#include "back_end/risc_v.h"
#include "util/io.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char current_output_dir[128];

void configure_ast(bool simple)
{
    struct ast_dump_config ast_config = {
        .omit_pos = simple,
        .colored  = 1
    };
    ast_dump_set_config(&ast_config);
}

void __gen_test(const char *path, unused const char *filename, FILE *out_stream)
{
    char elf_path[256] = {0};
    snprintf(elf_path, sizeof (elf_path) - 1, "%s/__gen.o", current_output_dir);

    struct codegen_output output = {0};
    back_end_init(&output);

    struct ir_unit ir = gen_ir(path);
    ir_opt_reorder(&ir);
    ir_dump_unit(stdout, &ir);
    back_end_gen(&ir);
    ir_unit_cleanup(&ir);

    back_end_emit(&output, elf_path);

    char buf[8192 * 16];
    system_read(buf, "%s -D --section=.text %s", __target_objdump, elf_path);

    fputs(buf, out_stream);
}

int gen_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __gen_test);
}

int main()
{
    cfg_dir("gen", current_output_dir);
    configure_ast(/*simple=*/0);

    do_on_each_file("gen", gen_test);

    return 1;
}