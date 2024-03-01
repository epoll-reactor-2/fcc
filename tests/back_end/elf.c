/* elf.c - Test cases for ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/elf.h"
#include "util/unreachable.h"
#include <errno.h>
#include <string.h>
#include <stdlib.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    struct elf_entry elf = {
        .arch     = ARCH_X86_64,
        .filename = "__elf.o"
    };
    struct elf_phdr phdr = {
        .type   = 1,
        .flags  = 6,
        .vaddr  = 0,
        .memsz  = 0,
        .filesz = 0
    };
    vector_push_back(elf.phdr, phdr);
    vector_push_back(elf.phdr, phdr);

    struct elf_shdr shdr = {
        .type   = 0x00,
        .addr   = 0x00,
        .link   = 0x00
    };
    vector_push_back(elf.shdr, shdr);

    elf_init(&elf);

    /*
    0x1141    addi    sp,sp,-16
    0xe422    sd      s0,8(sp)
    0x0800    addi    s0,sp,16
    0x4781    li      a5,0
    0x853e    mv      a0,a5
    0x6422    ld      s0,8(sp)
    0x0141    addi    sp,sp,16
    0x8082    ret
    */
    uint8_t code[] = {
        0x11, 0x41, 0xe4, 0x22,
        0x80, 0x00, 0x47, 0x81,
        0x85, 0x3e, 0x64, 0x22,
        0x01, 0x41, 0x80, 0x82
    };
    elf_put_code(code, sizeof (code));
    elf_exit();

    system("riscv64-linux-gnu-readelf -a __elf.o");
}
