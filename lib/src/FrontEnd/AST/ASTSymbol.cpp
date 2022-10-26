/* ASTSymbol.cpp - AST node to represent a variable name.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTSymbol.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTSymbol::ASTSymbol(std::string TheValue, unsigned TheLineNo,
                     unsigned TheColumnNo)
    : ASTNode(AST_SYMBOL, TheLineNo, TheColumnNo), Value(std::move(TheValue)) {}

void ASTSymbol::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTSymbol::GetName() const { return Value; }

} // namespace weak