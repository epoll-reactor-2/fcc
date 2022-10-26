/* ASTDump.hpp - AST dumper.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_DUMP_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_DUMP_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include <ostream>

namespace weak {

/// Stringify AST.
void ASTDump(ASTNode *RootNode, std::ostream &OutStream);

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_DUMP_HPP