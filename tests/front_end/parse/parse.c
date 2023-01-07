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

void tokens_cleanup(tok_array_t *toks) {
    for (uint64_t i = 0; i < toks->count; ++i) {
        tok_t *t = &toks->data[i];
        if (t->data)
            free(t->data);
    }
}

void extract_expected_ast(FILE *mem, FILE *file)
{
    char   *line = NULL;
    size_t  len = 0;
    ssize_t read = 0;

    while ((read = getline(&line, &len, file)) != -1) {
        if (read <= 3) {
            continue;
        }
        if (strncmp(line, "//", 2) == 0) {
            char *ptr = line + 2;
            while (*ptr != '\n' && *ptr != '\0') {
                fputc(*ptr++, mem);
            }
            fputc('\n', mem);
            fflush(mem);
        }
    }
    free(line);
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
    fseek(yyin, 0, SEEK_SET);

    char   *expected = NULL;
    char   *generated = NULL;
    size_t  _ = 0;
    FILE   *ast_stream = open_memstream(&expected, &_);
    FILE   *dump_stream = open_memstream(&generated, &_);

    extract_expected_ast(ast_stream, yyin);

    tok_array_t *toks = lex_consumed_tokens();

    if (!setjmp(weak_fatal_error_buf)) {
        ast_node_t *ast = parse(toks->data, toks->data + toks->count);
        ast_dump(dump_stream, ast);
        ast_node_cleanup(ast);

        if (strcmp(expected, generated) != 0) {
            printf("AST's mismatch:\n%s\ngot,\n%s\nexpected\n", generated, expected);
            return false;
        }
    } else {
        printf("Fatal error occurred: ");
        return false;
    }

    yylex_destroy();
    tokens_cleanup(toks);
    fclose(ast_stream);
    fclose(dump_stream);
    free(expected);
    free(generated);

    return true;
}

int main()
{
    int ret = 0;
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
        ret = -1;
        goto exit;
    }

    sprintf(cwd + strlen(cwd), "/parser");

    DIR *dir_iterator = opendir(cwd);
    struct dirent *dir;

    if (!dir_iterator) {
        perror("opendir()");
        ret = -1;
        goto exit;
    }

    while ((dir = readdir(dir_iterator)) != NULL) {
        if (dir->d_type == DT_DIR)
            continue;

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

            ret = -1;
            goto exit;
        }
    }

    closedir(dir_iterator);
exit:
    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);
    free(err_buf);
    free(warn_buf);
    return ret;
}