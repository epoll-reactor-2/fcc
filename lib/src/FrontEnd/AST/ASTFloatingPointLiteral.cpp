/* ASTFloatingPointLiteral.cpp - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFloatingPointLiteral.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTFloatingPointLiteral::ASTFloatingPointLiteral(float TheValue,
                                                 unsigned TheLineNo,
                                                 unsigned TheColumnNo)
    : ASTNode(AST_FLOATING_POINT_LITERAL, TheLineNo, TheColumnNo),
      Value(TheValue) {}

void ASTFloatingPointLiteral::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

float ASTFloatingPointLiteral::GetValue() const { return Value; }

} // namespace weak