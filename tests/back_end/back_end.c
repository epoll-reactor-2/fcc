/* back_end.c - Test cases for back end interface.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */
#include "back_end/elf.h"
#include "back_end/back_end.h"
#include "back_end/risc_v.h"
#include "util/io.h"
#include "utils/test_utils.h"
#include <asm-generic/unistd.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char current_output_dir[128];

void run(const char *path)
{
    system_run("%s -a %s", __target_readelf, path);
    system_run("%s -D %s", __target_objdump, path);

    int code = system_run("%s %s", __target_exec, path);

    printf("*** RISC-V file exited with code %d\n\n", WEXITSTATUS(code));
}

int main()
{
    cfg_dir("elf", current_output_dir);
    char elf_path[256] = {0};
    snprintf(elf_path, sizeof (elf_path) - 1, "%s/__elf.o", current_output_dir);

    struct codegen_output output = {0};

    back_end_init(&output);

    back_end_emit_sym("fn_1", 0);
    back_end_emit_sym("fn_2", 4);
    back_end_emit_sym("fn_3", 8);

    back_end_native_syscall_1(__NR_exit, 123);

    back_end_emit(&output, elf_path);

    run(elf_path);

    return 0;
}