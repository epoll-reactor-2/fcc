/* test_utils.h - Assertion functions for testing.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#undef NDEBUG
#include <assert.h>
#include <string.h>

#define ASSERT_TRUE(expr) \
  assert((expr));

#define ASSERT_FALSE(expr) \
  assert(!(expr));

#define ASSERT_EQ(lhs, rhs) \
  assert((lhs) == (rhs));

#define ASSERT_STREQ(lhs, rhs) \
  assert(strcmp((lhs), (rhs)) == 0);
