/* Lexical.h - String utilities.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_LEXICAL_H
#define WEAK_COMPILER_UTILITY_LEXICAL_H

#include <string>

namespace weak {

/// Get human-readable number representation like
/// 1'st, 2'nd, 3'rd.
std::string OrdinalNumeral(signed Num);

} // namespace weak

#endif // WEAK_COMPILER_UTILITY_LEXICAL_H