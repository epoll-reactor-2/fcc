/* compiler.h - Compiler-specific tricks.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef FCC_UTIL_COMPILER_H
#define FCC_UTIL_COMPILER_H

#if defined(__GNUC__) || defined(__llvm__) || defined(__INTEL_COMPILER)
# define __fcc_gnu_exts 1
#endif

#define noreturn                _Noreturn
#if defined(__fcc_gnu_exts)
# define likely(x)              __builtin_expect(!!(x), 1)
# define unlikely(x)            __builtin_expect(!!(x), 0)
# define wur                    __attribute__ ((warn_unused_result))
# define noinline               __attribute__ ((noinline))
# define really_inline          inline __attribute__ ((always_inline))
# define unused                 __attribute__ ((unused))
# define fmt(...)               __attribute__ ((format (printf, ##__VA_ARGS__)))
# define packed                 __attribute__((packed))
#else
# define likely(x)
# define unlikely(x)
# define wur
# define noinline
# define really_inline
# define unused
# define fmt(...)
# define packed
#endif

#define __fcc_to_string(x) #x

#ifdef CONFIG_USE_LOG
# define __fcc_debug(block) block
#else
# define __fcc_debug(block)
#endif /* CONFIG_USE_LOG */

#ifdef CONFIG_USE_LOG
# define __fcc_debug_msg(fmt, ...) do { \
    printf("%s@%d:    " fmt, __FILE__, __LINE__, ##__VA_ARGS__); \
 } while (0);
#else
# define __fcc_debug_msg(fmt, ...)
#endif /* CONFIG_USE_LOG */

#define __fcc_array_size(x) (sizeof ((x)) / sizeof (*(x)))

#endif // FCC_UTIL_COMPILER_H