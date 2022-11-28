/* ASTNode.cpp - Basic AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

ASTNode::ASTNode(ASTType Type, unsigned LineNo, unsigned ColumnNo)
  : mType(Type)
  , mLineNo(LineNo)
  , mColumnNo(ColumnNo) {}

ASTType ASTNode::Type() const {
  return mType;
}

bool ASTNode::Is(ASTType T) const {
  return mType == T;
}

unsigned ASTNode::LineNo() const {
  return mLineNo;
}

unsigned ASTNode::ColumnNo() const {
  return mColumnNo;
}

} // namespace weak