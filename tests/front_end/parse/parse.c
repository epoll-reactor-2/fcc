/* parse.c - Test case for parser.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast.h"
#include "front_end/ast/ast_dump.h"
#include "front_end/parse/parse.h"
#include "utils/test_utils.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void __parse_test(const char *path, const char *filename, FILE *out_stream)
{
    (void) filename;

    struct ast_node *ast = gen_ast(path);
    ast_dump(out_stream, ast);
    ast_node_cleanup(ast);
}

int parse_test(const char *path, const char *filename)
{
    (void) filename;

    return compare_with_comment(path, filename, __parse_test);
}

int main()
{
    return do_on_each_file("parser", parse_test);
}
