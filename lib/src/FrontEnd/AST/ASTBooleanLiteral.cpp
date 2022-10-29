/* ASTBooleanLiteral.cpp - AST node to represent a boolean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBooleanLiteral.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTBooleanLiteral::ASTBooleanLiteral(bool Value, unsigned LineNo,
                                     unsigned ColumnNo)
    : ASTNode(AST_BOOLEAN_LITERAL, LineNo, ColumnNo), mValue(Value) {}

void ASTBooleanLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

bool ASTBooleanLiteral::Value() const { return mValue; }

} // namespace weak