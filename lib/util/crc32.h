/* crc32.h - Сyclic redundancy check.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTIL_CRC32_H
#define WEAK_COMPILER_UTIL_CRC32_H

#include <stdint.h>

uint32_t crc32_string(const char *mem);

#endif // WEAK_COMPILER_UTIL_CRC32_H