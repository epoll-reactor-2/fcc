/* Files.cpp - Utilities to work with files.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "Utility/Files.h"
#include <fstream>

std::string weak::FileAsString(std::string_view Path) {
  std::ifstream File;
  File.open(Path.data());
  if (File.fail())
    throw std::runtime_error("Cannot open " + std::string(Path));

  return {(std::istreambuf_iterator<char>(File)),
          (std::istreambuf_iterator<char>())};
}