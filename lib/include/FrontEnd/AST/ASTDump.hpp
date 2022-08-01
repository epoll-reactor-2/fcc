/* ASTDump.hpp - helper function to dump AST to stdout.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_DUMP_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_DUMP_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include <memory>

namespace weak {
namespace frontEnd {

/// Show visual representation of Syntax Tree beginning with
/// RootNode.
void ASTDump(const std::unique_ptr<ASTNode> &RootNode, std::ostream &OutStream);

/// \copydoc ASTDump(const std::unique_ptr<ASTNode> &, std::ostream &)
void ASTDump(const ASTNode *RootNode, std::ostream &OutStream);

} // namespace frontEnd
} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_DUMP_HPP
