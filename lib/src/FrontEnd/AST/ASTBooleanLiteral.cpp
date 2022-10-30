/* ASTBooleanLiteral.cpp - AST node to represent a boolean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBool.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTBool::ASTBool(bool Value, unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_BOOLEAN_LITERAL, LineNo, ColumnNo), mValue(Value) {}

void ASTBool::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

bool ASTBool::Value() const { return mValue; }

} // namespace weak