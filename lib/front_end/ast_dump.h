/* ast_dump.h - AST stringify function.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef FCC_FRONTEND_AST_AST_DUMP_H
#define FCC_FRONTEND_AST_AST_DUMP_H

#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>

struct ast_dump_config {
    bool omit_pos;
    bool colored;
};

struct ast_node;

void ast_dump_set_config(struct ast_dump_config *new);

/** Write AST represented as string to given file or memory stream.

    \return 0 on success
            1 on following errors:
              - memory stream is NULL
              - ast is NULL
              - any required non-NULL AST node is NULL */
int32_t ast_dump(FILE *mem, struct ast_node *ast);

#endif // FCC_FRONTEND_AST_AST_DUMP_H
