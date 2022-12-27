/* data_type.c - Test case for data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/data_type.h"
#include "utils/test_utils.h"

int main()
{
    ASSERT_STREQ(data_type_to_string(DT_UNKNOWN), "unknown");
    ASSERT_STREQ(data_type_to_string(DT_VOID), "void");
    ASSERT_STREQ(data_type_to_string(DT_INT), "int");
    ASSERT_STREQ(data_type_to_string(DT_FLOAT), "float");
    ASSERT_STREQ(data_type_to_string(DT_CHAR), "char");
    ASSERT_STREQ(data_type_to_string(DT_BOOL), "bool");
    ASSERT_STREQ(data_type_to_string(DT_STRUCT), "struct");
}