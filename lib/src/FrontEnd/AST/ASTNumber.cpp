/* ASTNumber.cpp - AST node to represent a integer number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTNumber.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTNumber::ASTNumber(signed Value, unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_INTEGER_LITERAL, LineNo, ColumnNo)
    , mValue(Value) {}

void ASTNumber::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

signed ASTNumber::Value() const {
  return mValue;
}

} // namespace weak