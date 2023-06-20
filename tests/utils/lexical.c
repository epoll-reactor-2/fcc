/* lexical.c - Test case for text formatting utils.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "util/lexical.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    char buf[32];
    ordinal_numeral(1, buf);
    ASSERT_STREQ(buf, "1'st");
    ordinal_numeral(2, buf);
    ASSERT_STREQ(buf, "2'nd");
    ordinal_numeral(3, buf);
    ASSERT_STREQ(buf, "3'rd");
    ordinal_numeral(4, buf);
    ASSERT_STREQ(buf, "4'th");
    ordinal_numeral(5, buf);
    ASSERT_STREQ(buf, "5'th");
    ordinal_numeral(11, buf);
    ASSERT_STREQ(buf, "11'th");
    ordinal_numeral(111, buf);
    ASSERT_STREQ(buf, "111'th");
    ordinal_numeral(1111, buf);
    ASSERT_STREQ(buf, "1111'th");
    ordinal_numeral(3141244124, buf);
    ASSERT_STREQ(buf, "3141244124'th");
    ordinal_numeral(99999999999999, buf);
    ASSERT_STREQ(buf, "99999999999999'th");
    ordinal_numeral(555555554333, buf);
    ASSERT_STREQ(buf, "555555554333'rd");
}