/* ASTArrayAccess.cpp - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTArrayAccess.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTArrayAccess::ASTArrayAccess(std::string TheSymbolName, ASTNode *TheIndex,
                               unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_ARRAY_ACCESS, TheLineNo, TheColumnNo),
      SymbolName(TheSymbolName), Index(TheIndex) {}

ASTArrayAccess::~ASTArrayAccess() { delete Index; }

void ASTArrayAccess::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTArrayAccess::GetSymbolName() const { return SymbolName; }

ASTNode *ASTArrayAccess::GetIndex() const { return Index; }

} // namespace weak