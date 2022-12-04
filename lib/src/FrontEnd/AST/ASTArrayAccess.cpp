/* ASTArrayAccess.cpp - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTArrayAccess.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTArrayAccess::ASTArrayAccess(
  std::string            Name,
  std::vector<ASTNode *> Indices,
  unsigned               TheLineNo,
  unsigned               TheColumnNo
) : ASTNode(AST_ARRAY_ACCESS, TheLineNo, TheColumnNo)
  , mName(std::move(Name))
  , mIndices(std::move(Indices)) {}

ASTArrayAccess::~ASTArrayAccess() {
  for (auto *I : mIndices)
    delete I;
}

void ASTArrayAccess::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

const std::string &ASTArrayAccess::Name() const {
  return mName;
}

const std::vector<ASTNode *> &ASTArrayAccess::Indices() const {
  return mIndices;
}

} // namespace weak