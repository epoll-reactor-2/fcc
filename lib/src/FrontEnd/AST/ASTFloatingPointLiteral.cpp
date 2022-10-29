/* ASTFloatingPointLiteral.cpp - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFloatingPointLiteral.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTFloatingPointLiteral::ASTFloatingPointLiteral(float Value, unsigned LineNo,
                                                 unsigned ColumnNo)
    : ASTNode(AST_FLOATING_POINT_LITERAL, LineNo, ColumnNo), mValue(Value) {}

void ASTFloatingPointLiteral::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

float ASTFloatingPointLiteral::Value() const { return mValue; }

} // namespace weak