/* parse.c - Test case for parser.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/ast/ast_dump.h"
#include "front_end/lex/lex.h"
#include "front_end/parse/parse.h"
#include "utility/diagnostic.h"
#include "utils/test_utils.h"
#include <dirent.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

static bool is_directory(const char *path)
{
    return strcmp(path,  ".") == 0
        || strcmp(path, "..") == 0;
}

int main()
{
    static char *err_buf = NULL;
    static char *warn_buf = NULL;
    static size_t err_buf_len = 0;
    static size_t warn_buf_len = 0;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    ASSERT_TRUE(diag_error_memstream != NULL);
    ASSERT_TRUE(diag_warn_memstream != NULL);

    char cwd[512];
    if (getcwd(cwd, sizeof(cwd)) == NULL) {
        perror("getcwd()");
        return 1;
    }

    sprintf(cwd + strlen(cwd), "/parser");

    DIR *dir_iterator = opendir(cwd);
    struct dirent *dir;

    if (!dir_iterator) {
        perror("opendir()");
        return -1;
    }

    while ((dir = readdir(dir_iterator)) != NULL) {
        if (is_directory(dir->d_name)) {
            continue;
        }

        char buf[1024];
        sprintf(buf, "%s/%s", cwd, dir->d_name);

        printf("Testing file %s...\n", buf);
        fflush(stdout);

        lex_cleanup_global_state();
        lex_init_global_state();

        yyin = fopen(buf, "r");
        if (yyin == NULL) {
            perror("fopen()");
            return -1;
        }
        yylex();

        tok_array_t *consumed = lex_consumed_tokens();
        bool fatal_error = false;

        if (!setjmp(weak_fatal_error_buf)) {
            ast_node_t *ast = parse(consumed->data, consumed->data + consumed->count);
            ast_node_cleanup(ast);
        } else {
            printf("Fatal error occurred: ");
            fatal_error = true;
        }

        if (warn_buf)
            puts(warn_buf);

        if (err_buf)
            puts(err_buf);

        if (fatal_error || err_buf)
            return 1;

        yylex_destroy();
    }

    closedir(dir_iterator);
}