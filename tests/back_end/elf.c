/* elf.c - Test cases for ELF header generator.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/elf.h"
#include "back_end/risc_v.h"
#include "util/unreachable.h"
#include <errno.h>
#include <string.h>
#include <stdlib.h>

int risc_v_xor   (int rd, int rs1, int rs2);

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    /*
    0x1141    addi    sp,sp,-16
    0xe422    sd      s0,8(sp)
    0x4781    li      a5,0
    0x853e    mv      a0,a5
    0x6422    ld      s0,8(sp)
    0x0141    addi    sp,sp,16
    0x8082    ret
    */

    int32_t c = risc_v_xor(risc_v_reg_s4, risc_v_reg_s6, risc_v_reg_s2);
    uint8_t *__c = (uint8_t *) &c;
    unused uint8_t risc_v_code[] = {
        0x41, 0x11, 0x22, 0xe4,
        0x81, 0x47,
        0x3e, 0x85, 0x22, 0x64,
        0x41, 0x01, 0x82, 0x80,
        __c[0],
        __c[1],
        __c[2],
        __c[3],
    };
    /*
    48 c7 c03 c00 00  mov $0x3c, %rax
    48 31 ff          xor %rdi, %rdi
    0f 05             syscall
    */
    unused uint8_t x86_64_code[] = {
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00,
        0x48, 0x31, 0xff,
        0x0f, 0x05
    };

    struct codegen_output output = {0};

    hashmap_init(&output.fn_offsets, 512);
    hashmap_put (&output.fn_offsets, (uint64_t) "__example_sym_1", 0x00);
    hashmap_put (&output.fn_offsets, (uint64_t) "__example_sym_2", 0x02);
    hashmap_put (&output.fn_offsets, (uint64_t) "__example_sym_3", 0x04);
    hashmap_put (&output.fn_offsets, (uint64_t) "__example_sym_4", 0x06);
    hashmap_put (&output.fn_offsets, (uint64_t) "__example_sym_5", 0x08);
    hashmap_put (&output.fn_offsets, (uint64_t) "__example_sym_6", 0x0A);
 
    for (uint64_t i = 0; i < sizeof (risc_v_code); ++i) {
        vector_push_back(output.instrs, risc_v_code[i]);
    }

    struct elf_entry elf = {
        .arch     = ARCH_RISC_V,
        .filename = "__elf.o",
        .output   = output
    };

    elf_init(&elf);
    elf_exit();

    system("riscv64-linux-gnu-readelf -a __elf.o");
    system("riscv64-linux-gnu-objdump -D __elf.o");
}
