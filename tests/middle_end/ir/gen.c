/* gen.c - Tests for IR generator.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir/ir_dump.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void __gen_test(const char *path, unused const char *filename, FILE *out_stream)
{
    struct ir_unit ir = gen_ir(path);
    ir_dump_unit(out_stream, &ir);
    ir_unit_cleanup(&ir);
}

int gen_test(const char *path, const char *filename)
{
    return compare_with_comment(path, filename, __gen_test);
}

int main()
{
    return do_on_each_file("ir_gen", gen_test);
}