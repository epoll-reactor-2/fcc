/* test_utils.h - Assertion functions for testing.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#undef NDEBUG
#include "front_end/lex/lex.h"
#include "front_end/ana/ana.h"
#include "front_end/ast/ast.h"
#include "front_end/parse/parse.h"
#include "middle_end/ir/ir.h"
#include "middle_end/ir/gen.h"
#include "util/compiler.h"
#include "util/diagnostic.h"
#include "util/lexical.h"
#include <assert.h>
#include <dirent.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>

#define ASSERT_TRUE(expr)   assert((expr));
#define ASSERT_FALSE(expr)  assert(!(expr));
#define ASSERT_EQ(lhs, rhs) assert((lhs) == (rhs));

#define ASSERT_STREQ(lhs, rhs) do {     \
    int32_t rc = strcmp((lhs), (rhs));  \
    if (rc != 0) {                      \
        fprintf(stderr, "%s@%d: Strings mismatch:\n\t`%s` and\n\t`%s`\n", __FILE__, __LINE__, (lhs), (rhs)); \
        return rc;                      \
    }                                   \
} while(0);

extern FILE *yyin;
extern int yylex();
extern int yylex_destroy();

void tokens_cleanup(tok_array_t *toks)
{
    for (uint64_t i = 0; i < toks->count; ++i) {
        struct token *t = &toks->data[i];
        if (t->data)
            free(t->data);
    }
    vector_free(*toks);
}

/* Get string represented as comment placed in the very
   beginning of file. For example,
   // A,
   // b,
   // c.
   String "A,\nb,\nc." will be issued in output stream.

   NOTE: Requires opened `yyin` stream.
   NOTE: If `filename` is not null, appends
         it to generate full compiler report. */
void get_init_comment(FILE *in, FILE *out, const char *filename)
{
    char   *line = NULL;
    size_t  len  = 0;
    ssize_t read = 0;

    fseek(in, 0, SEEK_SET);

    while ((read = getline(&line, &len, in)) != -1) {
        if (read <= 3)
            continue;

        if (strncmp(line, "//", 2) == 0) {
            if (filename)
                fprintf(out, "%s: ", filename);

            char *ptr = line + 2;
            while (*ptr != '\n' && *ptr != '\0') {
                fputc(*ptr++, out);
            }
            fputc('\n', out);
        }
    }
    free(line);
    fflush(out);
}

void set_cwd(char cwd[512], const char *tests_dir)
{
    if (!getcwd(cwd, 512))
        weak_unreachable("Cannot get current dir: %s", strerror(errno));

    size_t cwd_len = strlen(cwd);

    snprintf(cwd + cwd_len, 512 - cwd_len, "%s", tests_dir);
}

int compare_with_comment(
    const char *path,
    const char *filename,
    void (*fn)(
        const char * /* path */,
        const char * /* filename */,
        FILE       * /* out_stream */
    )
) {
    int     rc               = 0;
    char   *expected         = NULL;
    char   *generated        = NULL;
    size_t  _                = 0;
    FILE   *expected_stream  = open_memstream(&expected, &_);
    FILE   *generated_stream = open_memstream(&generated, &_);

    if (!setjmp(weak_fatal_error_buf)) {
        fn(path, filename, generated_stream);

        get_init_comment(yyin, expected_stream, NULL);

        fflush(generated_stream);

        if (strcmp(expected, generated) != 0) {
            printf(
                "%sMismatch:%s\n%s\ngot,\n%s\nexpected\n",
                color_red, color_end,
                generated, expected
            );
            rc = -1;
            goto exit;
        }
    } else {
        /* Error, will be printed in main. */
        return -1;
    }

exit:
    fclose(expected_stream);
    fclose(generated_stream);
    free(expected);
    free(generated);

    return rc;
}

/* NOTE: `yylex` is opened in gen_tokens() and closed after `callback`
         call. User should not touch this stream in their tests. */
int do_on_each_file(
    const char  *dir,
    int        (*callback)(
        const char */* path */,
        const char */* filename */
    )
) {
    char    cwd     [ 512] = {0};
    char    full_dir[ 512] = {0};
    char    fname   [1024] = {0};
    int     rc             =  0 ;
    DIR    *it             = NULL;
    struct  dirent    *d   = NULL;

    snprintf(full_dir, sizeof (full_dir) - 1, "/inputs/%s", dir);

    set_cwd(cwd, full_dir);

    printf("Opening working directory: %s\n", cwd);

    it = opendir(cwd);
    if (!it)
        weak_unreachable("Cannot open current dir: %s", strerror(errno));

    while ((d = readdir(it))) {
        switch (d->d_type) {
        case DT_DIR:
            continue; /* Skip. */
        case DT_REG:
        case DT_LNK:
            break; /* Ok. */
        default:
            weak_unreachable("File or symlink expected as test input.");
        }

        if (strstr(d->d_name, "disabled_") != NULL)
            continue;

        printf("* %s... ", d->d_name);
        fflush(stdout);

        snprintf(fname, sizeof (fname), "%s/%s", cwd, d->d_name);

        weak_set_source_filename(fname);

        if (callback(fname, d->d_name) < 0) {
            rc = -1;
            yylex_destroy();
            fclose(yyin);
            goto exit;
        } else {
            printf("%sSuccess!%s\n", color_green, color_end);
            fflush(stdout);
        }

        fclose(yyin);
        yylex_destroy();

        memset(fname, 0, sizeof (fname));
    }

exit:
    closedir(it);
    return rc;
}



void create_dir(const char *name)
{
    struct stat st = {0};
    if (stat(name, &st) == -1) {
        if (mkdir(name, 0777) < 0) {
            perror("mkdir()");
            abort();
        }
    }
}

void cfg_dir(const char *name, char *curr_out_dir)
{
    snprintf(curr_out_dir, 127, "outputs/%s", name);

    create_dir("outputs");
    create_dir(curr_out_dir);
}



/* Depends on flex output state, `lex_consumed_tokens` should
   return tokens for current file opened by lex. */
tok_array_t *gen_tokens(const char *filename)
{
    lex_reset_state();
    lex_init_state();

    if (!yyin) yyin = fopen(filename, "r");
    else yyin = freopen(filename, "r", yyin);
    if (yyin == NULL)
        weak_unreachable("Cannot open file `%s`", filename);

    yylex();
    fseek(yyin, 0, SEEK_SET);
    weak_set_source_stream(yyin);

    return lex_consumed_tokens();
}

struct ast_node *gen_ast(const char *filename)
{
    tok_array_t *tokens = gen_tokens(filename);
    struct ast_node *ast = parse(tokens->data, tokens->data + tokens->count);
    tokens_cleanup(tokens);
    return ast;
}

struct ir_unit gen_ir(const char *filename)
{
    struct ast_node *ast = gen_ast(filename);

    /* Preconditions for IR generator. */
    ana_var_usage(ast);
    ana_fn(ast);
    ana_type(ast);

    struct ir_unit unit = ir_gen(ast);
    ast_node_cleanup(ast);
    return unit;
}