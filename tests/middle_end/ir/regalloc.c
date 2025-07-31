/* regalloc.c - Test cases for regalloc.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir_dump.h"
#include "middle_end/ir/regalloc.h"
#include "middle_end/opt/opt.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void __reg_alloc_test(const char *path, unused const char *filename, FILE *out_stream)
{
    struct ir_unit ir = gen_ir(path);
    ir_opt_reorder(&ir);
    ir_reg_alloc(&ir, /*hardware_regs=*/8);
    ir_dump_unit(stdout, &ir);
    ir_dump_unit(out_stream, &ir);
    ir_unit_cleanup(&ir);
}

int reg_alloc_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __reg_alloc_test);
}

int main()
{
    return do_on_each_file("regalloc", reg_alloc_test);
}
