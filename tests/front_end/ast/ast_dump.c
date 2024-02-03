/* ast_dump.c - Test cases for AST stringify function.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "util/alloc.h"
#include "utils/test_utils.h"
#include <stdlib.h>
#include <string.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    char *buf = NULL;
    size_t size = 0;
    FILE *stream = open_memstream(&buf, &size);

    struct ast_node **nums = weak_calloc(5, sizeof(struct ast_node *));
    nums[0] = ast_num_init(1, 2, 3);
    nums[1] = ast_num_init(1, 2, 3);
    nums[2] = ast_num_init(1, 2, 3);
    nums[3] = ast_implicit_cast_init(
                  D_T_INT,
                  D_T_FLOAT,
                  ast_num_init(1, 2, 3),
                  3, 4
              );
    nums[4] = ast_compound_init(0, NULL, 0, 0);

    struct ast_node *block = ast_compound_init(5, nums, 0, 0);
    ast_dump(stream, block);
    ast_node_cleanup(block);

    ASSERT_STREQ(
        buf,
        "CompoundStmt <line:0, col:0>\n"
        "  Number <line:2, col:3> 1\n"
        "  Number <line:2, col:3> 1\n"
        "  Number <line:2, col:3> 1\n"
        "  ImplicitCastExpr <line:3, col:4> int -> float\n"
        "    Number <line:2, col:3> 1\n"
        "  CompoundStmt <line:0, col:0>\n"
    );

    fclose(stream);
    free(buf);
}