/* alloc.h - Safe memory allocation functions.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_ALLOC_H
#define WEAK_COMPILER_UTILITY_ALLOC_H

#include "utility/compiler.h"
#include <stddef.h>

#if GNU_ATTRIBUTE(returns_nonnull) && GNU_ATTRIBUTE(warn_unused_result) && GNU_ATTRIBUTE(alloc_size)
#define __weak_attr_malloc__  __attribute__((returns_nonnull, warn_unused_result, malloc, alloc_size(1)))
#define __weak_attr_calloc__  __attribute__((returns_nonnull, warn_unused_result, malloc, alloc_size(1, 2)))
#define __weak_attr_realloc__ __attribute__((returns_nonnull, warn_unused_result, alloc_size(2)))
#else
#define __weak_attr_malloc__
#define __weak_attr_calloc__
#define __weak_attr_realloc__
#endif

__weak_attr_malloc__ void *weak_malloc(size_t size);
__weak_attr_calloc__ void *weak_calloc(size_t nmemb, size_t size);
__weak_attr_realloc__ void *weak_realloc(void *addr, size_t size);

/// Used to reduce #include <stdlib.h> bloat.
void weak_free(void *addr);

#endif // WEAK_COMPILER_UTILITY_ALLOC_H