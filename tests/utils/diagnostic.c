/* diagnostic.c - Test case for diagnostic functions.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "utility/diagnostic.h"
#include "utils/test_utils.h"
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

void sighandler(int sig)
{
    if (sig == SIGABRT) {
        fprintf(stderr, "Caught SIGABRT on compile error, now exit normally...\n");
        fflush(stderr);
        exit(0);
    }
}

void diagnostics_stderr_test()
{
    ASSERT_TRUE(diag_error_memstream == NULL);
    ASSERT_TRUE(diag_warn_memstream == NULL);

    weak_compile_warn(0, 0, "Hello, ");
    weak_compile_error(1, 1, "World!");
}

void diagnostics_memstream_test()
{
    static char *err_buf = NULL;
    static char *warn_buf = NULL;
    static size_t err_buf_len = 0;
    static size_t warn_buf_len = 0;

    diag_error_memstream = open_memstream(&err_buf, &err_buf_len);
    diag_warn_memstream = open_memstream(&warn_buf, &warn_buf_len);

    ASSERT_TRUE(diag_error_memstream != NULL);
    ASSERT_TRUE(diag_warn_memstream != NULL);

    weak_compile_warn(0, 0, "Hello, ");
    weak_compile_warn(0, 0, "Hello, ");

    ASSERT_TRUE(warn_buf_len > 0);
    ASSERT_STREQ("Warning at line 0, column 0: Hello, \n"
                 "Warning at line 0, column 0: Hello, \n", warn_buf);

    weak_compile_error(1, 1, "World!");
    weak_compile_error(1, 1, "World!");

    ASSERT_TRUE(warn_buf_len > 0);
    ASSERT_STREQ("Warning at line 0, column 0: Hello, \n"
                 "Warning at line 0, column 0: Hello, \n", warn_buf);
    ASSERT_STREQ("Error at line 1, column 1: World!\n"
                 "Error at line 1, column 1: World!\n", err_buf);

    fclose(diag_error_memstream);
    fclose(diag_warn_memstream);

    diag_error_memstream = NULL;
    diag_warn_memstream = NULL;
}

int main()
{
    signal(SIGABRT, sighandler);

    diagnostics_memstream_test();
    diagnostics_stderr_test();
}