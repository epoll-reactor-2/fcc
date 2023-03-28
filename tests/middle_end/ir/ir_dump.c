/* ir_dump.c - Tests for IR dump function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_dump.h"
#include "utility/vector.h"
#include "utility/unreachable.h"
#include "utils/test_utils.h"
#include <stdio.h>

#define TEST_START_INFO { printf("Testing %s()... ", __FUNCTION__); fflush(stdout); }
#define TEST_END_INFO   { printf(" Success!\n"); fflush(stdout); }

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

typedef vector_t(ir_node_t) ir_array_t;

void ir_dump_basic(FILE *stream, char **expected)
{
    TEST_START_INFO

    ir_array_t args = {0};
    vector_push_back(args, ir_alloca_init(D_T_INT, 0));
    vector_push_back(args, ir_alloca_init(D_T_CHAR, 1));
    vector_push_back(args, ir_alloca_init(D_T_FLOAT, 2));
    vector_push_back(args, ir_alloca_init(D_T_INT, 3));

    /// State should be reset before the start
    /// of each function body.
    ir_reset_internal_state();
    ir_array_t body = {0};
    vector_push_back(body, ir_alloca_init(D_T_VOID, 0));
    vector_push_back(body, ir_alloca_init(D_T_VOID, 1));
    vector_push_back(body, ir_store_imm_init(0, 123));
    vector_push_back(body, ir_store_var_init(1, 0));

    ir_func_decl_t func = {
        .name      = "decl_f",
        .args_size = args.count,
        .args      = args.data,
        .body_size = body.count,
        .body      = body.data
    };

    ir_dump(stream, &func);

    *expected = 
        "fun decl_f(alloca int %0, alloca char %1, alloca float %2, alloca int %3):\n"
        "       0:   alloca void %0\n"
        "       1:   alloca void %1\n"
        "       2:   store %0 $123\n"
        "       3:   store %1 %0\n";

    vector_foreach(args, i) {
        ir_node_cleanup(args.data[i]);
    }
    vector_foreach(body, i) {
        ir_node_cleanup(body.data[i]);
    }

    vector_free(args);
    vector_free(body);

    TEST_END_INFO
}

void ir_dump_call(FILE *stream, char **expected)
{
    TEST_START_INFO

    ir_array_t args = {0};
    vector_push_back(args, ir_sym_init(1));
    vector_push_back(args, ir_sym_init(2));
    vector_push_back(args, ir_imm_init(3));

    ir_reset_internal_state();
    ir_array_t calls = {0};
    vector_push_back(calls, ir_func_call_init("f1", args.count, args.data));
    vector_push_back(calls, ir_func_call_init("f2", args.count, args.data));
    vector_push_back(calls, ir_func_call_init("f3", args.count, args.data));
    vector_push_back(calls, ir_func_call_init("f4", args.count, args.data));
    vector_push_back(calls, ir_func_call_init("f5", args.count, args.data));

    ir_func_decl_t decl = {
        .name      = "decl_f",
        .args_size = 0,
        .args      = NULL,
        .body_size = calls.count,
        .body      = calls.data
    };

    ir_dump(stream, &decl);

    *expected =
        "fun decl_f():\n"
        "       0:   call f1(%1, %2, $3)\n"
        "       1:   call f2(%1, %2, $3)\n"
        "       2:   call f3(%1, %2, $3)\n"
        "       3:   call f4(%1, %2, $3)\n"
        "       4:   call f5(%1, %2, $3)\n";

    vector_foreach(args, i) {
        ir_node_cleanup(args.data[i]);
    }
    vector_foreach(calls, i) {
        ir_node_cleanup(calls.data[i]);
    }

    vector_free(args);
    vector_free(calls);

    TEST_END_INFO
}

int32_t ir_dump_test()
{
    void (*test_fns[])() = {
        ir_dump_basic,
        ir_dump_call
    };

    for (uint64_t i = 0; i < sizeof(test_fns) / sizeof(*test_fns); ++i) {
        char *buf = NULL;
        size_t size = 0;
        FILE *stream = open_memstream(&buf, &size);
        char *expected = NULL;

        if (!stream) weak_unreachable("Cannot open file");

        test_fns[i](stream, &expected);
        fflush(stream);

        /// Implicitly returns on mismatch.
        ASSERT_STREQ(buf, expected);
        fclose(stream);
        free(buf);
    }

    return 0;
}

int main()
{
    if (ir_dump_test() < 0) return -1;
}