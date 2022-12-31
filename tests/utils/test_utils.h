/* test_utils.h - Assertion functions for testing.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#undef NDEBUG
#include "utility/compiler.h"
#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#define ASSERT_TRUE(expr) \
  assert((expr));

#define ASSERT_FALSE(expr) \
  assert(!(expr));

#define ASSERT_EQ(lhs, rhs) \
  assert((lhs) == (rhs));

#define ASSERT_STREQ(lhs, rhs) do {   \
  int32_t rc = strcmp((lhs), (rhs));  \
  if (rc != 0) {                      \
    fprintf(stderr, "%s: Strings mismatch:\n\t`%s` and\n\t`%s`\n", SOURCE_LINE, (lhs), (rhs)); \
  }                                   \
} while(0);

//  assert(strcmp((lhs), (rhs)) == 0);
