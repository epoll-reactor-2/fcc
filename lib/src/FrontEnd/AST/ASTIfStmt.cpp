/* ASTIfStmt.cpp - AST node to represent a if or if-else statements.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTIfStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTIfStmt::ASTIfStmt(ASTNode *Condition, ASTCompoundStmt *ThenBody,
                     ASTCompoundStmt *ElseBody, unsigned LineNo,
                     unsigned ColumnNo)
    : ASTNode(AST_IF_STMT, LineNo, ColumnNo), mCondition(Condition),
      mThenBody(ThenBody), mElseBody(ElseBody) {}

ASTIfStmt::~ASTIfStmt() {
  delete mCondition;
  delete mThenBody;
  delete mElseBody;
}

void ASTIfStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTIfStmt::Condition() const { return mCondition; }

ASTCompoundStmt *ASTIfStmt::ThenBody() const { return mThenBody; }

ASTCompoundStmt *ASTIfStmt::ElseBody() const { return mElseBody; }

} // namespace weak