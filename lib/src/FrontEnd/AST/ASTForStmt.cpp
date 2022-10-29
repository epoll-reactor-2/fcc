/* ASTForStmt.cpp - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTForStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTForStmt::ASTForStmt(ASTNode *Init, ASTNode *Condition, ASTNode *Increment,
                       ASTCompoundStmt *Body, unsigned LineNo,
                       unsigned ColumnNo)
    : ASTNode(AST_FOR_STMT, LineNo, ColumnNo), mInit(Init),
      mCondition(Condition), mIncrement(Increment), mBody(Body) {}

ASTForStmt::~ASTForStmt() {
  delete mInit;
  delete mCondition;
  delete mIncrement;
  delete mBody;
}

void ASTForStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTForStmt::Init() const { return mInit; }

ASTNode *ASTForStmt::Condition() const { return mCondition; }

ASTNode *ASTForStmt::Increment() const { return mIncrement; }

ASTCompoundStmt *ASTForStmt::Body() const { return mBody; }

} // namespace weak