/* compiler.h - Compiler-specific tricks.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_COMPILER_H
#define WEAK_COMPILER_UTILITY_COMPILER_H

#if defined(__GNUC__) || defined(__llvm__) || defined(__INTEL_COMPILER)
# define GNU_EXTENSIONS 1
#endif

#if defined(GNU_EXTENSIONS) && defined(__has_attribute)
# define GNU_ATTRIBUTE(attr) __has_attribute(attr)
#else
# define GNU_ATTRIBUTE(attr) 0
#endif

#define MACRO_MKSTRING(x) #x
#define MACRO_TOSTRING(x) MACRO_MKSTRING(x)

#define SOURCE_LINE __FILE__ "@" MACRO_TOSTRING(__LINE__)

#endif // WEAK_COMPILER_UTILITY_COMPILER_H