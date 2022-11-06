/* ASTFloat.cpp - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFloat.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTFloat::ASTFloat(float Value, unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_FLOATING_POINT_LITERAL, LineNo, ColumnNo), mValue(Value) {}

void ASTFloat::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

float ASTFloat::Value() const { return mValue; }

} // namespace weak