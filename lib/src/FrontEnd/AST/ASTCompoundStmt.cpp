/* ASTCompoundStmt.cpp - AST node to represent a block of code.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTCompoundStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTCompoundStmt::ASTCompoundStmt(std::vector<ASTNode *> &&TheStmts,
                                 unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_COMPOUND_STMT, TheLineNo, TheColumnNo),
      Stmts(std::move(TheStmts)) {}

ASTCompoundStmt::~ASTCompoundStmt() {
  for (ASTNode *S : Stmts)
    delete S;
}

void ASTCompoundStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::vector<ASTNode *> &ASTCompoundStmt::GetStmts() const {
  return Stmts;
}

} // namespace weak