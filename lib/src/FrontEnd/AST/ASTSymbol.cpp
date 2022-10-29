/* ASTSymbol.cpp - AST node to represent a variable name.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTSymbol.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTSymbol::ASTSymbol(std::string Value, unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_SYMBOL, LineNo, ColumnNo), mValue(std::move(Value)) {}

void ASTSymbol::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTSymbol::Name() const { return mValue; }

} // namespace weak