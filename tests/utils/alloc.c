/* alloc.c - Test case for allocation functions.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/alloc.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main() {
    {
        void *addr = weak_malloc(1);
        ASSERT_TRUE(addr);
        weak_free(addr);
    }

    {
        void *addr = weak_calloc(1, 1);
        ASSERT_TRUE(addr);
        weak_free(addr);
    }

    {
        void *addr = weak_malloc(1);
        addr = weak_realloc(addr, 2);
        ASSERT_TRUE(addr);
        weak_free(addr);
    }
}