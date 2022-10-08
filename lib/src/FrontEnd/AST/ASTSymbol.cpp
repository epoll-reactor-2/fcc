/* ASTSymbol.cpp - AST node to represent a variable name.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTSymbol.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {
namespace frontEnd {

ASTSymbol::ASTSymbol(std::string TheValue, unsigned TheLineNo,
                     unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Value(std::move(TheValue)) {}

ASTType ASTSymbol::GetASTType() const { return ASTType::SYMBOL; }

void ASTSymbol::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTSymbol::GetName() const { return Value; }

} // namespace frontEnd
} // namespace weak