/* ASTIntegerLiteral.cpp - AST node to represent a integer number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTIntegerLiteral.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTIntegerLiteral::ASTIntegerLiteral(signed Value, unsigned LineNo,
                                     unsigned ColumnNo)
    : ASTNode(AST_INTEGER_LITERAL, LineNo, ColumnNo), mValue(Value) {}

void ASTIntegerLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

signed ASTIntegerLiteral::Value() const { return mValue; }

} // namespace weak