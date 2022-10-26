/* ASTArrayAccess.cpp - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTArrayAccess.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTArrayAccess::ASTArrayAccess(std::string TheSymbolName, ASTNode *TheIndex,
                               unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), SymbolName(TheSymbolName),
      Index(TheIndex) {}

ASTArrayAccess::~ASTArrayAccess() { delete Index; }

ASTType ASTArrayAccess::GetASTType() const { return AST_ARRAY_ACCESS; }

void ASTArrayAccess::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTArrayAccess::GetSymbolName() const { return SymbolName; }

ASTNode *ASTArrayAccess::GetIndex() const { return Index; }

} // namespace weak