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

int main()
{
    ir_array_t ir = {0};
    vector_push_back(ir, ir_alloca_init(D_T_VOID, 0));
    vector_push_back(ir, ir_store_init(1, ir_label_init(0)));

    ir_dump(stdout, ir.data, 2);
}