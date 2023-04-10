/* compiler.h - Compiler-specific tricks.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_COMPILER_H
#define WEAK_COMPILER_UTILITY_COMPILER_H

#if defined(__GNUC__) || defined(__llvm__) || defined(__INTEL_COMPILER)
# define __weak_gnu_exts 1
#endif

#if defined(__weak_gnu_exts) && defined(__has_attribute)
# define __weak_likely(x)       __builtin_expect(!!(x), 1)
# define __weak_unlikely(x)     __builtin_expect(!!(x), 0)
# define __weak_wur__           __attribute__((warn_unused_result))
# define __weak_noinline__      __attribute__((noinline))
# define __weak_really_inline__ inline __attribute__((always_inline))
#else
# define __weak_likely(x)
# define __weak_unlikely(x)
# define __weak_wur__
# define __weak_noinline__
# define __weak_really_inline__
#endif

#define __weak_to_string(x) #x

#endif // WEAK_COMPILER_UTILITY_COMPILER_H