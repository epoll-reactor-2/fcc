/* ASTStringLiteral.cpp - AST node to represent a string literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTString.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTString::ASTString(std::string Value, unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_STRING_LITERAL, LineNo, ColumnNo), mValue(std::move(Value)) {}

void ASTString::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTString::Value() const { return mValue; }

} // namespace weak