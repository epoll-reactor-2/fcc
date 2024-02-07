/* report.c - Example usage of generating report about codebase compilation.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ana/ana.h"
#include "front_end/ast/ast.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stdio.h>

extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

char cwd[512] = {0};
bool create_warn_dump = 0;
bool create_err_dump = 0;

void(*analysis_fn)(struct ast_node *) = NULL;

/* There we create file for each compiled program, but format is
   up to you.

   Another suggested format in one file:
   file1: E<N, N>: ...
   file1: E<N, N>: ...
   file1: W<N, N>: ...
   file2: W<N, N>: ...  */
bool analysis_test(const char *path, const char *filename)
{
    if (create_err_dump) {
        char out[512] = {0};
        snprintf(out, 511, "%s/%s.log", cwd, filename);
        diag_error_memstream = fopen(out, "w");
    }

    if (create_warn_dump) {
        char out[512] = {0};
        snprintf(out, 511, "%s/%s.log", cwd, filename);
        diag_warn_memstream = fopen(out, "w");

        printf("Warn stream: %p\n", diag_warn_memstream);
    }

    struct ast_node *ast = gen_ast(path);

    if (!setjmp(weak_fatal_error_buf))
        analysis_fn(ast);

exit:
    ast_node_cleanup(ast);
    yylex_destroy();

    if (create_err_dump)
        fclose(diag_error_memstream);

    if (create_warn_dump)
        fclose(diag_warn_memstream);

    return 1;
}

int run(const char *dir)
{
    snprintf(cwd, 511, "dumps/%s", dir);
    create_dir(cwd);

    return do_on_each_file(dir, analysis_test);
}

void configure()
{
    struct diag_config config = {
        .ignore_warns  = 0,
        .show_location = 0
    };
    weak_diag_set_config(&config);

    create_dir("dumps");
    create_dir("dumps/var_ana");
}

int main()
{
    configure();

    analysis_fn = analysis_functions_analysis;
    create_warn_dump = 0;
    create_err_dump = 1;
    if (run("fn_ana") < 0)
        return -1;

    create_warn_dump = 0;
    create_err_dump = 1;
    analysis_fn = analysis_variable_use_analysis;
    if (run("var_ana/errors") < 0)
        return -1;

    create_warn_dump = 1;
    create_err_dump = 0;
    analysis_fn = analysis_variable_use_analysis;
    if (run("var_ana/warns") < 0)
        return -1;

    create_warn_dump = 0;
    create_err_dump = 1;
    analysis_fn = analysis_type_analysis;
    if (run("type_errors") < 0)
        return -1;

    return 0;
}