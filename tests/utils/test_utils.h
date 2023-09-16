/* test_utils.h - Assertion functions for testing.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#undef NDEBUG
#include <dirent.h>
#include <stdbool.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "front_end/lex/lex.h"
#include "util/diagnostic.h"
#include "util/compiler.h"

#define ASSERT_TRUE(expr)   assert((expr));
#define ASSERT_FALSE(expr)  assert(!(expr));
#define ASSERT_EQ(lhs, rhs) assert((lhs) == (rhs));

#define TEST_START_INFO { printf("Testing %s()... ", __FUNCTION__); fflush(stdout); }
#define TEST_END_INFO   { printf(" Success!\n"); fflush(stdout); }

#define ASSERT_STREQ(lhs, rhs) do {     \
    int32_t rc = strcmp((lhs), (rhs));  \
    if (rc != 0) {                      \
        fprintf(stderr, "%s@%d: Strings mismatch:\n\t`%s` and\n\t`%s`\n", __FILE__, __LINE__, (lhs), (rhs)); \
        return rc;                      \
    }                                   \
} while(0);

__weak_really_inline void tokens_cleanup(tok_array_t *toks)
{
    for (uint64_t i = 0; i < toks->count; ++i) {
        struct token *t = &toks->data[i];
        if (t->data)
            free(t->data);
    }
    vector_free(*toks);
}

/// Get string represented as comment placed in the very
/// begin of file. For example,
/// // A,
/// // b,
/// // c.
/// String "A,\nb,\nc." will be issued in output stream.
__weak_really_inline void extract_assertion_comment(FILE *in, FILE *out)
{
    char   *line = NULL;
    size_t  len  = 0;
    ssize_t read = 0;

    while ((read = getline(&line, &len, in)) != -1) {
        if (read <= 3)
            continue;

        if (strncmp(line, "//", 2) == 0) {
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

__weak_really_inline void extract_compiler_messages(const char *filename, FILE *in, FILE *out)
{
    char   *line = NULL;
    size_t  len  = 0;
    ssize_t read = 0;

    while ((read = getline(&line, &len, in)) != -1) {
        if (read <= 3)
            continue;

        if (strncmp(line, "//", 2) == 0) {
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

__weak_really_inline void set_cwd(char cwd[static 512], const char *tests_dir)
{
    if (!getcwd(cwd, 512))
        weak_unreachable("Cannot get current dir: %s", strerror(errno));

    size_t cwd_len = strlen(cwd);

    snprintf(cwd + cwd_len, 512 - cwd_len, "%s", tests_dir);
}

__weak_really_inline bool do_on_each_file(const char *tests_dir, bool(*callback)(const char *))
{
    char    cwd  [ 512] = {0};
    char    fname[1024] = {0};
    bool    success     =  1 ;
    DIR    *it          = NULL;
    struct  dirent *dir = NULL;

    set_cwd(cwd, tests_dir);

    printf("Opening working directory: %s\n", cwd);

    it = opendir(cwd);
    if (!it)
        weak_unreachable("Cannot open current dir: %s", strerror(errno));

    while ((dir = readdir(it))) {
        switch (dir->d_type) {
        case DT_DIR:
            continue; /// Skip.
        case DT_REG:
        case DT_LNK:
            break; /// Ok.
        default:
            weak_unreachable("File or symlink expected as test input.");
        }

        printf("Testing file %s... ", dir->d_name);
        fflush(stdout);

        snprintf(fname, sizeof (fname), "%s/%s", cwd, dir->d_name);

        weak_set_source_filename(fname);

        if (!callback(fname)) {
            success = 0;
            goto exit;
        }

        memset(fname, 0, sizeof (fname));
    }

exit:
    closedir(it);
    return success;
}