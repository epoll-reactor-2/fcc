/* risc_v_instr.c - Test cases for RISC-V instruction coding.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/risc_v_encode.h"
#include "util/lexical.h"
#include <stdio.h>
#include <stdlib.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void test(const char *name, int code, int expect)
{
    if (code != expect) {
        printf(
            "%sError:%s %s expected 0x%08x, got 0x%08x\n",
            color_red, color_end, name, expect, code
        );
        exit(-1);
    } else {
        printf("%s%s%s -> 0x%08x\n", color_green, name, color_end, code);
    }
}

/* https://luplab.gitlab.io/rvcodecjs/#q=srli+s1,+s1,+1&abi=false&isa=AUTO */
int main() {
    test("jalr s1, s1, s2", risc_v_jalr  (risc_v_reg_s1, risc_v_reg_s1, 0), 0x000484e7);
    test("srl  s1, s1, s2", risc_v_srl   (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x0124d4b3);
    test("add  s1, s1, s2", risc_v_add   (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x012484b3);
    test("sub  s5, s4, s2", risc_v_sub   (risc_v_reg_s5, risc_v_reg_s4, risc_v_reg_s2), 0x412a0ab3);
    test("or   s4, s6, s2", risc_v_or    (risc_v_reg_s4, risc_v_reg_s6, risc_v_reg_s2), 0x012b6a33);
    test("mul  s4, s6, s2", risc_v_mul   (risc_v_reg_s4, risc_v_reg_s6, risc_v_reg_s2), 0x032b0a33);
    test("div  s4, s6, s2", risc_v_div   (risc_v_reg_s4, risc_v_reg_s6, risc_v_reg_s2), 0x032b4a33);
    test("mod  s4, s6, s2", risc_v_mod   (risc_v_reg_s4, risc_v_reg_s6, risc_v_reg_s2), 0x032b6a33);
    test("xor  s4, s6, s2", risc_v_xor   (risc_v_reg_s4, risc_v_reg_s6, risc_v_reg_s2), 0x012b4a33);
    test("and  s1, s1, s2", risc_v_and   (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x0124f4b3);
    test("sll  s1, s1, s2", risc_v_sll   (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x012494b3);
    test("srl  s1, s1, s2", risc_v_srl   (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x0124d4b3);
    test("sra  s1, s1, s2", risc_v_sra   (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x4124d4b3);
    test("slt  s1, s1, s2", risc_v_slt   (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x0124a4b3);
    test("sltu s1, s1, s2", risc_v_sltu  (risc_v_reg_s1, risc_v_reg_s1, risc_v_reg_s2), 0x0124b4b3);
    test("ecall          ", risc_v_ecall (), 0x00000073);
    test("ebreak         ", risc_v_ebreak(), 0x00200073);
    test("nop            ", risc_v_nop   (), 0x00000013);
    /*
    test("ret            ", risc_v_ret   (), 0x00000067);
    */
}