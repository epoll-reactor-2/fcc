/* ASTDoWhileStmt.cpp - AST node to represent a do-while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTDoWhileStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTDoWhileStmt::ASTDoWhileStmt(ASTCompoundStmt *Body, ASTNode *Condition,
                               unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_DO_WHILE_STMT, LineNo, ColumnNo), mBody(Body),
      mCondition(Condition) {}

ASTDoWhileStmt::~ASTDoWhileStmt() {
  delete mBody;
  delete mCondition;
}

void ASTDoWhileStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTCompoundStmt *ASTDoWhileStmt::Body() const { return std::move(mBody); }

ASTNode *ASTDoWhileStmt::Condition() const { return mCondition; }

} // namespace weak