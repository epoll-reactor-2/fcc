/* Lexical.cpp - String utilities.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "Utility/Lexical.h"

std::string weak::OrdinalNumeral(signed Num) {
  std::string O = std::to_string(Num) + "'";
  switch (Num) {
  case 1:  O += "st"; break;
  case 2:  O += "nd"; break;
  default: O += "th"; break;
  }
  return O;
}