/* ASTCharLiteral.cpp - AST node to represent a single character.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTCharLiteral.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {
namespace frontEnd {

ASTCharLiteral::ASTCharLiteral(char TheValue, unsigned TheLineNo,
                               unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Value(TheValue) {}

ASTType ASTCharLiteral::GetASTType() const { return ASTType::CHAR_LITERAL; }

void ASTCharLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

char ASTCharLiteral::GetValue() const { return Value; }

} // namespace frontEnd
} // namespace weak