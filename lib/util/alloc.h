/* alloc.h - Safe memory allocation functions.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTIL_ALLOC_H
#define WEAK_COMPILER_UTIL_ALLOC_H

#include <stddef.h>
#include "util/compiler.h"

#if __has_attribute(returns_nonnull) && __has_attribute(warn_unused_result) && __has_attribute(alloc_size)
#define __weak_malloc  __attribute__((returns_nonnull, warn_unused_result, malloc, alloc_size(1)))
#define __weak_calloc  __attribute__((returns_nonnull, warn_unused_result, malloc, alloc_size(1, 2)))
#define __weak_realloc __attribute__((returns_nonnull, warn_unused_result, alloc_size(2)))
#else
#define __weak_malloc
#define __weak_calloc
#define __weak_realloc
#endif

__weak_malloc  __weak_wur void *weak_malloc(size_t size);
__weak_calloc  __weak_wur void *weak_calloc(size_t nmemb, size_t size);
__weak_realloc __weak_wur void *weak_realloc(void *addr, size_t size);
               __weak_wur void *weak_alloca(size_t size);

/// Used to reduce #include <stdlib.h> bloat.
void weak_free(void *addr);

#endif // WEAK_COMPILER_UTIL_ALLOC_H