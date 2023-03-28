/* ast_dump.c - Test cases for AST stringify function.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_dump.h"
#include "front_end/ast/ast_compound.h"
#include "front_end/ast/ast_num.h"
#include "utility/alloc.h"
#include "utils/test_utils.h"
#include <stdlib.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    char *buf = NULL;
    size_t size = 0;
    FILE *stream = open_memstream(&buf, &size);

    ast_node_t **nums = weak_calloc(5, sizeof(ast_node_t *));
    nums[0] = ast_num_init(1, 2, 3);
    nums[1] = ast_num_init(1, 2, 3);
    nums[2] = ast_num_init(1, 2, 3);
    nums[3] = ast_num_init(1, 2, 3);
    nums[4] = ast_compound_init(0, NULL, 0, 0);

    ast_node_t *block = ast_compound_init(5, nums, 0, 0);
    ast_dump(stream, block);
    ast_node_cleanup(block);

    ASSERT_STREQ(
        buf,
        "CompoundStmt <line:0, col:0>\n"
        "  Number <line:2, col:3> 1\n"
        "  Number <line:2, col:3> 1\n"
        "  Number <line:2, col:3> 1\n"
        "  Number <line:2, col:3> 1\n"
        "  CompoundStmt <line:0, col:0>\n"
    );

    fclose(stream);
    free(buf);
}