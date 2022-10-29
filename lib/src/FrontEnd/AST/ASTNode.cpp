/* ASTNode.cpp - Basic AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

ASTNode::ASTNode(ASTType TheType, unsigned TheLineNo, unsigned TheColumnNo)
    : Type(TheType), LineNo(TheLineNo), ColumnNo(TheColumnNo) {}

ASTType ASTNode::GetASTType() const { return Type; }

bool ASTNode::Is(ASTType T) const { return Type == T; }

unsigned ASTNode::GetLineNo() const { return LineNo; }

unsigned ASTNode::GetColumnNo() const { return ColumnNo; }

} // namespace weak