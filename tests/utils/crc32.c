/* crc32.h - Test case for CRC-32 function.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/crc32.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    ASSERT_EQ(crc32_string(""), 0);
    ASSERT_EQ(crc32_string("123"), 0x884863d2);
}