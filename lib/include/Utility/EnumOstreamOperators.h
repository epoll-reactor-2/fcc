/* EnumOstreamOperators.h - std::ostream out operators for all enums.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTType.h"
#include "FrontEnd/Lex/DataType.h"
#include "FrontEnd/Lex/TokenType.h"
#include <ostream>

std::ostream &operator<<(std::ostream &, weak::ASTType);
std::ostream &operator<<(std::ostream &, weak::TokenType);
std::ostream &operator<<(std::ostream &, weak::DataType);