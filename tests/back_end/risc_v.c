/* risc_v.c - Test cases for RISC-V codegen.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v.h"
#include "back_end/elf.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/type.h"
#include "middle_end/opt/opt.h"
#include "util/diagnostic.h"
#include "util/lexical.h"
#include "utils/test_utils.h"
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char current_output_dir[128];

void do_opt(struct ir_unit *unit)
{
    ir_opt_reorder(unit);
    ir_opt_arith(unit);
    ir_dump_unit(stdout, unit);

    struct ir_node *it = unit->fn_decls;
    while (it) {
        ir_cfg_build(it->ir);
        it = it->next;
    }
}

int run(const char *out_path)
{
    char buf[512] = {0};
    int code = 0;

#define __run(fmt, ...) \
    { snprintf(buf, sizeof (buf) - 1, fmt, ##__VA_ARGS__); \
      code = system(buf); }

    __run("riscv64-linux-gnu-readelf -a %s", out_path);
    __run("riscv64-linux-gnu-objdump -D %s", out_path);
    __run("chmod +x %s", out_path);
    __run("qemu-riscv64 %s", out_path);

    return WEXITSTATUS(code);

#undef __run_cmd
}

int gen(struct ir_unit *unit, const char *filename)
{
    char out_path[256] = {0};

    snprintf(out_path, 255, "%s/%s.o", current_output_dir, filename);

    struct codegen_output output = {0};
    hashmap_init(&output.fn_offsets, 512);

    risc_v_gen(&output, unit);

    struct elf_entry elf = {
        .arch     = ARCH_RISC_V,
        .filename = out_path,
        .output   = output
    };
    elf_init(&elf);
    elf_exit();

    hashmap_destroy(&output.fn_offsets);
    vector_free(output.instrs);

    return run(out_path);
}

void __risc_v_test(const char *path, const char *filename, FILE *out_stream)
{
    struct ir_unit ir = gen_ir(path);

    ir_type_pass(&ir);
    do_opt(&ir);
    int code = gen(&ir, filename);
    ir_unit_cleanup(&ir);

    fprintf(out_stream, "%d\n", code);
}

int risc_v_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __risc_v_test);
}

int main()
{
    cfg_dir("risc_v", current_output_dir);
    return do_on_each_file("risc_v", risc_v_test);
}