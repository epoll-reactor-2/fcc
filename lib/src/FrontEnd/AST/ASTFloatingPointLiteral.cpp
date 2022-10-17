/* ASTFloatingPointLiteral.cpp - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFloatingPointLiteral.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTFloatingPointLiteral::ASTFloatingPointLiteral(float TheValue,
                                                 unsigned TheLineNo,
                                                 unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Value(TheValue) {}

ASTType ASTFloatingPointLiteral::GetASTType() const {
  return ASTType::FLOATING_POINT_LITERAL;
}

void ASTFloatingPointLiteral::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

float ASTFloatingPointLiteral::GetValue() const { return Value; }

} // namespace weak