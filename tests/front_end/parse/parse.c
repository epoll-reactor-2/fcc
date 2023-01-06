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

void extract_expected_ast(FILE *memstream, FILE *file)
{
    char   *line = NULL;
    size_t  len = 0;
    ssize_t read = 0;

    while ((read = getline(&line, &len, file)) != -1) {
        if (read <= 3)
            continue;
        if (strncmp(line, "//", 2) == 0) {
            char *ptr = line + 2;
            while (*ptr != '\n' && *ptr != '\0') {
                fputc(*ptr++, memstream);
            }
            fputc('\n', memstream);
            fflush(memstream);
        }
    }
}

/// Parse file and compare result with expected.
///
/// \pre    Reset lexer state.
/// \return true on success, false on failure.
bool parse_test(const char *filename)
{
    yyin = fopen(filename, "r");
    if (yyin == NULL) {
        perror("fopen()");
        return -1;
    }
    yylex();

    char  *expected_ast = NULL;
    size_t expected_ast_size = 0;
    char  *generated_ast = NULL;
    size_t generated_ast_size = 0;
    FILE  *memstream = open_memstream(&expected_ast, &expected_ast_size);
    FILE  *out_memstream = open_memstream(&generated_ast, &generated_ast_size);

    fseek(yyin, 0, SEEK_SET);
    extract_expected_ast(memstream, yyin);

    tok_array_t *consumed = lex_consumed_tokens();

    if (!setjmp(weak_fatal_error_buf)) {
        ast_node_t *ast = parse(consumed->data, consumed->data + consumed->count);
        ast_dump(out_memstream, ast);
        ast_node_cleanup(ast);

        if (strcmp(expected_ast, generated_ast) != 0) {
            printf("AST's mismatch:\n%s\ngot,\n%s\nexpected\n", generated_ast, expected_ast);
            return false;
        }
    } else {
        printf("Fatal error occurred: ");
        return false;
    }

    yylex_destroy();
    return true;
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

        lex_cleanup_global_state();
        lex_init_global_state();

        char filename[1024];
        sprintf(filename, "%s/%s", cwd, dir->d_name);

        printf("Testing file %s...\n", filename);
        fflush(stdout);

        if (!parse_test(filename)) {
            if (err_buf)
                printf("%s\n", err_buf);

            if (warn_buf)
                printf("%s\n", warn_buf);

            return 1;
        }

        yylex_destroy();
    }

    closedir(dir_iterator);
}