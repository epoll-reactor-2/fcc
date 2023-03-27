/* ir_dump.c - Tests for IR dump function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_dump.h"
#include "utility/vector.h"
#include <stdio.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

typedef vector_t(ir_node_t) ir_array_t;

void ir_dump_basic()
{
    ir_array_t args = {0};
    vector_push_back(args, ir_alloca_init(D_T_INT, 0));
    vector_push_back(args, ir_alloca_init(D_T_CHAR, 1));
    vector_push_back(args, ir_alloca_init(D_T_FLOAT, 2));
    vector_push_back(args, ir_alloca_init(D_T_INT, 3));

    /// State should be reest before the start
    /// of each function.
    ir_reset_internal_state();
    ir_array_t body = {0};
    vector_push_back(body, ir_alloca_init(D_T_VOID, 0));
    vector_push_back(body, ir_alloca_init(D_T_VOID, 1));
    vector_push_back(body, ir_store_imm_init(0, 123));
    vector_push_back(body, ir_store_var_init(1, 0));

    ir_func_decl_t func = {
        .name = "decl_f",
        .args_size = args.count,
        .args = args.data,
        .body_size = body.count ,
        .body = body.data
    };

    ir_dump(stdout, &func);
}

void ir_dump_call()
{
    ir_array_t args = {0};
    vector_push_back(args, ir_sym_init(1));
    vector_push_back(args, ir_sym_init(2));
    vector_push_back(args, ir_imm_init(3));

    ir_reset_internal_state();
    ir_node_t calls[] = {
        ir_func_call_init(
            "f1",
            args.count,
            args.data
        ),
        ir_func_call_init(
            "f2",
            args.count,
            args.data
        )
    };

    ir_func_decl_t decl = {
        .name = "decl_f",
        .args_size = 0,
        .args = NULL,
        .body_size = 2,
        .body = calls
    };

    ir_dump(stdout, &decl);
}

int main()
{
    ir_dump_basic();
    ir_dump_call();
}