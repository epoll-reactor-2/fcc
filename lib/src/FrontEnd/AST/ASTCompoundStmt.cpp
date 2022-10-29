/* ASTCompoundStmt.cpp - AST node to represent a block of code.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTCompoundStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTCompoundStmt::ASTCompoundStmt(std::vector<ASTNode *> &&Stmts,
                                 unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_COMPOUND_STMT, LineNo, ColumnNo), mStmts(std::move(Stmts)) {}

ASTCompoundStmt::~ASTCompoundStmt() {
  for (ASTNode *S : mStmts)
    delete S;
}

void ASTCompoundStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::vector<ASTNode *> &ASTCompoundStmt::Stmts() const { return mStmts; }

} // namespace weak