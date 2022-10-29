/* ASTCharLiteral.cpp - AST node to represent a single character.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTCharLiteral.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTCharLiteral::ASTCharLiteral(char TheValue, unsigned TheLineNo,
                               unsigned TheColumnNo)
    : ASTNode(AST_CHAR_LITERAL, TheLineNo, TheColumnNo), Value(TheValue) {}

void ASTCharLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

char ASTCharLiteral::GetValue() const { return Value; }

} // namespace weak