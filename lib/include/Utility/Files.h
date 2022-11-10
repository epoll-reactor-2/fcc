/* Files.h - Utilities to work with files.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_UTILITY_FILES_H
#define WEAK_COMPILER_UTILITY_FILES_H

#include <string>

namespace weak {

std::string FileAsString(std::string_view Path);

} // namespace weak

#endif // WEAK_COMPILER_UTILITY_FILES_H