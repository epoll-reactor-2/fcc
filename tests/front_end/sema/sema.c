/* sema.c - Test cases for semantic AST passes.
 * Copyright (C) 2024 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "front_end/sema/sema.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void (*sema_fn)(struct ast_node **);

void __sema_test(const char *path, const char *filename, FILE *out_stream)
{
    (void) filename;

    struct ast_node *ast = gen_ast(path);
    sema_fn(&ast);
    ast_dump(out_stream, ast);
    ast_node_cleanup(ast);
}

int sema_test(const char *path, const char *filename)
{
    (void) filename;

    return compare_with_comment(path, filename, __sema_test);
}

int run(const char *dir)
{
    return do_on_each_file(dir, sema_test);
}

int main()
{
    struct ast_dump_config config = {
        .omit_pos = 1,
        .colored  = 0
    };
    ast_dump_set_config(&config);

    sema_fn = sema_lower;
    if (run("sema_lower") < 0)
        return -1;

    sema_fn = sema_type;
    if (run("sema_type") < 0)
        return -1;
}