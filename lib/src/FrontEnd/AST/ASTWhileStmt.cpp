/* ASTWhileStmt.cpp - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTWhileStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTWhileStmt::ASTWhileStmt(ASTNode *Condition, ASTCompoundStmt *Body,
                           unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_WHILE_STMT, LineNo, ColumnNo), mCondition(Condition),
      mBody(Body) {}

ASTWhileStmt::~ASTWhileStmt() {
  delete mCondition;
  delete mBody;
}

void ASTWhileStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTWhileStmt::Condition() const { return mCondition; }

ASTCompoundStmt *ASTWhileStmt::Body() const { return mBody; }

} // namespace weak