/* ir_graph.c - Tests for IR graph build functions.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "middle_end/ir_graph.h"
#include "middle_end/ir.h"
#include "utils/test_utils.h"
#include <stdio.h>
#include <math.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void matrix_print(bool *mat, size_t row_size)
{
    for (size_t i = 0; i < row_size; ++i) {
        printf("[ ");
        for (size_t j = 0; j < row_size; ++j) {
            printf("%d ", mat[i * row_size + j]);
        }
        printf("]\n");
    }    
}

int main()
{
    printf("Testing IR graph...\n");

    struct ir_node ir[] = {
        ir_imm_init(1),
        ir_jump_init(4),
        ir_imm_init(1),
        ir_cond_init(
            ir_bin_init(
                TOK_PLUS,
                ir_imm_init(1),
                ir_imm_init(2)
            ),
            1
        ),
        ir_imm_init(1)
    };

    struct ir_graph graph = ir_graph_init(ir, 5);

    bool assertion[] = {
        0, 0, 0, 0, 0,
        1, 0, 0, 1, 0,
        0, 0, 0, 0, 0,
        0, 0, 1, 0, 0,
        0, 1, 0, 1, 0
    };

    ASSERT_EQ(memcmp(assertion, graph.adj_matrix, 5 * 5), 0);

    matrix_print(graph.adj_matrix, 5);

    ir_graph_cleanup(&graph);

    for (size_t i = 0; i < 5; ++i) {
        ir_node_cleanup(ir[i]);
    }
}