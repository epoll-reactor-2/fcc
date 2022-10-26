/* ASTIntegerLiteral.cpp - AST node to represent a integer number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTIntegerLiteral.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTIntegerLiteral::ASTIntegerLiteral(signed TheValue, unsigned TheLineNo,
                                     unsigned TheColumnNo)
    : ASTNode(AST_INTEGER_LITERAL, TheLineNo, TheColumnNo), Value(TheValue) {}

void ASTIntegerLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

signed ASTIntegerLiteral::GetValue() const { return Value; }

} // namespace weak