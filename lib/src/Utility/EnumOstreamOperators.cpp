/* EnumOstreamOperators.cpp - std::ostream out operators for all enums.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "Utility/EnumOstreamOperators.h"
#include "FrontEnd/Lex/Token.h"

std::ostream &operator<<(std::ostream &S, weak::ASTType E) {
  return S << weak::ASTTypeToString(E);
}

std::ostream &operator<<(std::ostream &S, weak::TokenType E) {
  return S << weak::TokenToString(E);
}

std::ostream &operator<<(std::ostream &S, weak::DataType E) {
  return S << weak::DataTypeToString(E);
}
