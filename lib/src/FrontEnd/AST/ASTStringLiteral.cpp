/* ASTStringLiteral.cpp - AST node to represent a string literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTStringLiteral.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTStringLiteral::ASTStringLiteral(std::string TheValue, unsigned TheLineNo,
                                   unsigned TheColumnNo)
    : ASTNode(AST_STRING_LITERAL, TheLineNo, TheColumnNo),
      Value(std::move(TheValue)) {}

void ASTStringLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTStringLiteral::GetValue() const { return Value; }

} // namespace weak