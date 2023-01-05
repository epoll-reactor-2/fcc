/* ast_dump.c - AST stringify function tests.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_dump.h"
#include "front_end/ast/ast_num.h"
#include "front_end/ast/ast_compound.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    ast_node_t *nums[] = {
        ast_num_init(1, 2, 3),
        ast_num_init(1, 2, 3),
        ast_num_init(1, 2, 3),
        ast_num_init(1, 2, 3),
        ast_compound_init(0, NULL, 0, 0)
    };
    ast_node_t *block = ast_compound_init(sizeof(nums) / sizeof(*nums), nums, 0, 0);
    ast_dump(stdout, block);
}