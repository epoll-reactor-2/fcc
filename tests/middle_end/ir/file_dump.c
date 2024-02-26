/* file_dump.c - Generate binary files with weak IR.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir.h"
#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/ir_bin.h"
#include "utils/test_utils.h"
#include <stdio.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int dump(const char *path, unused const char *filename)
{
    char out_path[256] = {0};
    snprintf(out_path, 255, "binary_dumps/%sir", filename);

    struct ir_unit ir = gen_ir(path);
    ir_write_binary(&ir, out_path);
    ir_unit_cleanup(&ir);

    struct ir_unit new_ir = ir_read_binary(out_path);
    puts("New unit:");
    ir_dump_unit(stdout, &new_ir);
    ir_unit_cleanup(&new_ir);

    return 0;
}

void configure()
{
    create_dir("binary_dumps");
}

int run()
{
    return do_on_each_file("ir_gen", dump);
}

int main()
{
    configure();
    return run();
}
