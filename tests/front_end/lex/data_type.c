/* data_type.c - Test case for data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "front_end/lex/data_type.h"
#include "utils/test_utils.h"

void *diag_error_memstream = NULL;
void *diag_warn_memstream = NULL;

int main()
{
    ASSERT_STREQ(data_type_to_string(D_T_UNKNOWN), "unknown");
    ASSERT_STREQ(data_type_to_string(D_T_VOID), "void");
    ASSERT_STREQ(data_type_to_string(D_T_INT), "int");
    ASSERT_STREQ(data_type_to_string(D_T_FLOAT), "float");
    ASSERT_STREQ(data_type_to_string(D_T_CHAR), "char");
    ASSERT_STREQ(data_type_to_string(D_T_BOOL), "boolean");
    ASSERT_STREQ(data_type_to_string(D_T_STRUCT), "struct");
}