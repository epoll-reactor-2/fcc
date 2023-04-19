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
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "front_end/lex/lex.h"
#include "utility/compiler.h"

#define ASSERT_TRUE(expr)   assert((expr));
#define ASSERT_FALSE(expr)  assert(!(expr));
#define ASSERT_EQ(lhs, rhs) assert((lhs) == (rhs));

#define ASSERT_STREQ(lhs, rhs) do {   \
  int32_t rc = strcmp((lhs), (rhs));  \
  if (rc != 0) {                      \
    fprintf(stderr, "%s@%d: Strings mismatch:\n\t`%s` and\n\t`%s`\n", __FILE__, __LINE__, (lhs), (rhs)); \
    return rc;                        \
  }                                   \
} while(0);

void tokens_cleanup(tok_array_t *toks) {
    for (uint64_t i = 0; i < toks->count; ++i) {
        tok_t *t = &toks->data[i];
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
void extract_assertion_comment(FILE *in, FILE *out)
{
    char   *line = NULL;
    size_t  len = 0;
    ssize_t read = 0;

    while ((read = getline(&line, &len, in)) != -1) {
        if (read <= 3) {
            continue;
        }
        if (strncmp(line, "//", 2) == 0) {
            char *ptr = line + 2;
            while (*ptr != '\n' && *ptr != '\0') {
                fputc_unlocked(*ptr++, out);
            }
            fputc_unlocked('\n', out);
        }
    }
    free(line);
    fflush(out);
}

bool do_on_each_file(const char *tests_dir, bool(*callback)(const char *))
{
    char cwd[512];
    bool success = true;

    if (getcwd(cwd, sizeof(cwd)) == NULL) {
        perror("getcwd()");
        return false;
    }

    sprintf(cwd + strlen(cwd), "%s", tests_dir);

    printf("cwd: %s\n", cwd);

    DIR *dir_iterator = opendir(cwd);
    struct dirent *dir;

    if (!dir_iterator) {
        perror("opendir()");
        return false;
    }

    while ((dir = readdir(dir_iterator)) != NULL) {
        if (dir->d_type == DT_DIR)
            continue;

        char filename[1024];
        sprintf(filename, "%s/%s", cwd, dir->d_name);

        printf("Testing file %s... ", filename);

        if (!callback(filename)) {
            success = false;
            goto exit;
        }
    }

exit:
    closedir(dir_iterator);
    return success;
}