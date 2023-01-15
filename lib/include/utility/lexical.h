/* lexical.h - Text formatting and so on.
 * Copyright (C) 2023 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_LEXICAL_H
#define WEAK_COMPILER_UTILITY_LEXICAL_H

#include <stdint.h>

/// \param[out] out Requiers at most (sizeof(uint64_t) * CHAR_BIT + 4) bytes
void ordinal_numeral(uint64_t num, char *out);

#endif // WEAK_COMPILER_UTILITY_LEXICAL_H