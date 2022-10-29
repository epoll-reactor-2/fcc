/* ASTDump.h - AST dumper.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_DUMP_H
#define WEAK_COMPILER_FRONTEND_AST_AST_DUMP_H

#include "FrontEnd/AST/ASTNode.h"
#include <ostream>

namespace weak {

/// Stringify AST.
void ASTDump(ASTNode *RootNode, std::ostream &OutStream);

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_DUMP_H