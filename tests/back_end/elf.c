/* elf.c - Test cases for ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/elf.h"
#include "util/unreachable.h"
#include <errno.h>
#include <string.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    elf_gen("/tmp/__elf.o", ARCH_RISC_V);
}