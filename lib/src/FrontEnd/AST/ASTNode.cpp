/* ASTNode.cpp - Basic AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTNode.hpp"

namespace weak {

ASTNode::ASTNode(unsigned TheLineNo, unsigned TheColumnNo)
    : LineNo(TheLineNo), ColumnNo(TheColumnNo) {}

ASTType ASTNode::GetASTType() const { return AST_BASE_NODE; }

unsigned ASTNode::GetLineNo() const { return LineNo; }

unsigned ASTNode::GetColumnNo() const { return ColumnNo; }

} // namespace weak