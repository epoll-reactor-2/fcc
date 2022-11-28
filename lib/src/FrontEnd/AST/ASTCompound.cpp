/* ASTCompound.cpp - AST node to represent a block of code.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTCompound::ASTCompound(
  std::vector<ASTNode *> Stmts,
  unsigned               LineNo,
  unsigned               ColumnNo
) : ASTNode(AST_COMPOUND_STMT, LineNo, ColumnNo)
  , mStmts(std::move(Stmts)) {}

ASTCompound::~ASTCompound() {
  for (ASTNode *S : mStmts)
    delete S;
}

void ASTCompound::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

const std::vector<ASTNode *> &ASTCompound::Stmts() const {
  return mStmts;
}

} // namespace weak