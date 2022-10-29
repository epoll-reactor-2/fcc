/* ASTBooleanLiteral.cpp - AST node to represent a boolean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBooleanLiteral.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTBooleanLiteral::ASTBooleanLiteral(bool TheValue, unsigned TheLineNo,
                                     unsigned TheColumnNo)
    : ASTNode(AST_BOOLEAN_LITERAL, TheLineNo, TheColumnNo), Value(TheValue) {}

void ASTBooleanLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

bool ASTBooleanLiteral::GetValue() const { return Value; }

} // namespace weak