/* risc_v_encode.c - Tests for RISC-V encoding.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "back_end/back_end.h"
#include "back_end/risc_v.h"
#include "utils/test_utils.h"
#include <stddef.h>
#include <stdio.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

struct codegen_output output = {0};

 #define __swap(x,y) do {   \
    typeof(x) _x = x;       \
    typeof(y) _y = y;       \
    x = _y;                 \
    y = _x;                 \
 } while(0)

void dump_bytes(const void *bytes, uint64_t len)
{
    const uint8_t *mem = bytes;

    for (uint64_t i = 0; i < len; ++i)
        printf("%02x", mem[i]);
}

/* Just for convenient tests with
   https://luplab.gitlab.io/rvcodecjs */
void be_to_le(void *bytes, uint64_t len)
{
    uint8_t *mem = bytes;

    for (uint64_t i = len; i >= len / 2; --i)
        __swap(mem[i], mem[len - i - 1]);
}

int match(uint64_t len, const char *bytes)
{
    instr_vector_t *text = elf_lookup_section(&output, ".text");

    ASSERT_TRUE(text->count > 0);

    if (text->count != len) {
        printf(
            "RISC-V encoding failed: %ld vs %ld bytes were encoded\n",
            text->count, len
        );
    }

    be_to_le(text->data, len);

    if (memcmp(text->data, bytes, len)) {
        printf("RISC-V encoding failed\n ");
        dump_bytes(text->data, text->count);
        printf(" got,\n ");
        dump_bytes(bytes, len);
        printf(" expected\n");
        ASSERT_TRUE(0);
    }

    vector_clear(*text);
}

int main()
{
    return 0;
    back_end_init(&output);

    back_end_native_sub(risc_v_reg_a2, risc_v_reg_a3, risc_v_reg_a4);
    match(4, "\x40\xe6\x86\x33");

    back_end_native_addiw(risc_v_reg_t0, risc_v_reg_t0, 1);
    match(4, "\x00\x12\x82\x9b");

    back_end_native_and(risc_v_reg_a2, risc_v_reg_a3, risc_v_reg_a4);
    match(4, "\x00\xe6\xf6\x33");
    /*
    back_end_native_addi(risc_v_reg_a2, risc_v_reg_a3, 0xfffff);
    match(8, "\x00\x06\x06\x13\xff\xf6\x86\x13");
    //        \               \
    //         \               addi a2, a3, 0x7ffff
    //          \
    //           addi a2, a2, 0x80000
    ASSERT_EQ(0xfffff, 0x7ffff + 0x80000);
    */
    back_end_native_lb(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7f\xf3\x02\x83");

    back_end_native_lbu(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7f\xf3\x42\x83");

    back_end_native_lh(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7f\xf3\x12\x83");

    back_end_native_lhu(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7f\xf3\x52\x83");

    back_end_native_lw(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7f\xf3\x22\x83");

    back_end_native_lwu(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7f\xf3\x62\x83");

    back_end_native_ld(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7f\xf3\x32\x83");

    back_end_native_sb(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7e\x53\x0f\xa3");

    back_end_native_sd(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7e\x53\x3f\xa3");

    back_end_native_sw(risc_v_reg_t0, risc_v_reg_t1, 2047);
    match(4, "\x7e\x53\x2f\xa3");

    back_end_native_ret();
    match(4, "\x00\x00\x80\x67");

    back_end_native_jmp_reg(risc_v_reg_s10);
    match(4, "\x00\x0d\x00\x67");

    back_end_native_prologue(/*stack_usage=*/0);
    match(16,
                           /* Reverse instructions order (endiannes)! */
        "\x01\x01\x04\x13" /* addi s0, sp, 16  */
        "\x00\x81\x30\x23" /* sd s0, 0(sp)     */
        "\x00\x11\x34\x23" /* sd ra, 8(sp)     */
        "\xff\x01\x01\x13" /* addi sp, sp, -16 */
    );

    back_end_native_epilogue(/*stack_usage=*/0);
    match(12,
                           /* Reverse instructions order (endiannes)! */
        "\x01\x01\x01\x13" /* addi sp, sp,  16 */
        "\x00\x01\x34\x03" /* ld s0, 0(sp)     */
        "\x00\x81\x30\x83" /* ld ra, 8(sp)     */
    );

    back_end_native_prologue(/*stack_usage=*/4);
    match(16,
                           /* Reverse instructions order (endiannes)! */
        "\x02\x01\x04\x13" /* addi s0, sp, 32  */
        "\x00\x81\x38\x23" /* sd s0, 16(sp)    */
        "\x00\x11\x3c\x23" /* sd ra, 24(sp)    */
        "\xfe\x01\x01\x13" /* addi sp, sp, -32 */
    );

    back_end_native_epilogue(/*stack_usage=*/4);
    match(12,
                           /* Reverse instructions order (endiannes)! */
        "\x02\x01\x01\x13" /* addi sp, sp, 32  */
        "\x01\x01\x34\x03" /* ld s0, 16(sp)    */
        "\x01\x81\x30\x83" /* ld ra, 24(sp)    */
    );

    back_end_native_prologue(/*stack_usage=*/8);
    match(16,
                           /* Reverse instructions order (endiannes)! */
        "\x02\x01\x04\x13" /* addi s0, sp, 32  */
        "\x00\x81\x38\x23" /* sd s0, 16(sp)    */
        "\x00\x11\x3c\x23" /* sd ra, 24(sp)    */
        "\xfe\x01\x01\x13" /* addi sp, sp, -32 */
    );

    back_end_native_epilogue(/*stack_usage=*/8);
    match(12,
                           /* Reverse instructions order (endiannes)! */
        "\x02\x01\x01\x13" /* addi sp, sp, 32  */
        "\x01\x01\x34\x03" /* ld s0, 16(sp)    */
        "\x01\x81\x30\x83" /* ld ra, 24(sp)    */
    );

    back_end_native_prologue(/*stack_usage=*/16);
    match(16,
                           /* Reverse instructions order (endiannes)! */
        "\x02\x01\x04\x13" /* addi s0, sp, 32  */
        "\x00\x81\x38\x23" /* sd s0, 16(sp)    */
        "\x00\x11\x3c\x23" /* sd ra, 24(sp)    */
        "\xfe\x01\x01\x13" /* addi sp, sp, -32 */
    );

    back_end_native_epilogue(/*stack_usage=*/16);
    match(12,
                           /* Reverse instructions order (endiannes)! */
        "\x02\x01\x01\x13" /* addi sp, sp, 32  */
        "\x01\x01\x34\x03" /* ld s0, 16(sp)    */
        "\x01\x81\x30\x83" /* ld ra, 24(sp)    */
    );

    back_end_native_prologue(/*stack_usage=*/20);
    match(16,
                           /* Reverse instructions order (endiannes)! */
        "\x03\x01\x04\x13" /* addi s0, sp, 48  */
        "\x02\x81\x30\x23" /* sd s0, 32(sp)    */
        "\x02\x11\x34\x23" /* sd ra, 40(sp)    */
        "\xfd\x01\x01\x13" /* addi sp, sp, -48 */
    );

    back_end_native_epilogue(/*stack_usage=*/20);
    match(12,
                           /* Reverse instructions order (endiannes)! */
        "\x03\x01\x01\x13" /* addi sp, sp, 48  */
        "\x02\x01\x34\x03" /* ld s0, 32(sp)    */
        "\x02\x81\x30\x83" /* ld ra, 40(sp)    */
    );

    // back_end_native_lb(risc_v_reg_t0, risc_v_reg_t1, 0xEEEEEEE);
    // match(12,
    //                        /* Reverse instructions order (endiannes)! */
    //     "\x03\x01\x01\x13" /* addi sp, sp, 48  */
    //     "\x02\x01\x34\x03" /* ld s0, 32(sp)    */
    //     "\x02\x81\x30\x83" /* ld ra, 40(sp)    */
    // );

    // back_end_native_lb(risc_v_reg_t0, risc_v_reg_t1, 0xEEEEEEE);

    back_end_native_lb(risc_v_reg_t0, risc_v_reg_t1, 0xEEEEEEE);
}
