/* diagnostic.c - Test case for diagnostic functions.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/diagnostic.h"
#include "utils/test_utils.h"
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int diagnostics_memstream_test()
{
    static char *err_buf = NULL;
    static char *warn_buf = NULL;
    static size_t err_buf_len = 0;
    static size_t warn_buf_len = 0;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    ASSERT_TRUE(diag_error_memstream != NULL);
    ASSERT_TRUE(diag_warn_memstream != NULL);

    weak_set_source_filename("text.txt");

    weak_compile_warn(0, 0, "Hello, ");
    weak_compile_warn(0, 0, "Hello, ");

    ASSERT_TRUE(warn_buf_len > 0);
    ASSERT_STREQ("text.txt: W<0:0>: Hello, \n"
                 "text.txt: W<0:0>: Hello, \n", warn_buf);

    if (!setjmp(weak_fatal_error_buf)) {
        weak_compile_error(1, 1, "World!");
        ASSERT_TRUE(false && "Must never reach here.");
    } else {
        ASSERT_TRUE(warn_buf_len > 0);
        ASSERT_STREQ("text.txt: W<0:0>: Hello, \n"
                     "text.txt: W<0:0>: Hello, \n", warn_buf);
        ASSERT_STREQ("text.txt: E<1:1>: World!\n", err_buf);

        fclose(diag_error_memstream);
        fclose(diag_warn_memstream);
        free(err_buf);
        free(warn_buf);
    }

    return 0;
}

int main()
{
    int rc = diagnostics_memstream_test();
    if (rc != 0)
        return rc;
}