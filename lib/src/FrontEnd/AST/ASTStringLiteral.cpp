/* ASTStringLiteral.cpp - AST node to represent a string literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTStringLiteral.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTStringLiteral::ASTStringLiteral(std::string TheValue, unsigned TheLineNo,
                                   unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Value(std::move(TheValue)) {}

ASTType ASTStringLiteral::GetASTType() const { return AST_STRING_LITERAL; }

void ASTStringLiteral::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTStringLiteral::GetValue() const { return Value; }

} // namespace weak