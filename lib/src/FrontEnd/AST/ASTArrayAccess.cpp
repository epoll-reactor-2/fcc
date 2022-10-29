/* ASTArrayAccess.cpp - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTArrayAccess.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTArrayAccess::ASTArrayAccess(std::string SymbolName, ASTNode *Index,
                               unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_ARRAY_ACCESS, TheLineNo, TheColumnNo),
      mSymbolName(SymbolName), mIndex(Index) {}

ASTArrayAccess::~ASTArrayAccess() { delete mIndex; }

void ASTArrayAccess::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTArrayAccess::SymbolName() const { return mSymbolName; }

ASTNode *ASTArrayAccess::Index() const { return mIndex; }

} // namespace weak