/* ASTArrayAccess.cpp - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTArrayAccess.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTArrayAccess::ASTArrayAccess(std::string TheSymbolName,
                               std::unique_ptr<ASTNode> &&TheIndex,
                               unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), SymbolName(TheSymbolName),
      Index(std::move(TheIndex)) {}

ASTType ASTArrayAccess::GetASTType() const { return ASTType::ARRAY_ACCESS; }

void ASTArrayAccess::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTArrayAccess::GetSymbolName() const { return SymbolName; }

const std::unique_ptr<ASTNode> &ASTArrayAccess::GetIndex() const {
  return Index;
}

} // namespace weak