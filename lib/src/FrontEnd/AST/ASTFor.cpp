/* ASTForStmt.cpp - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFor.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTFor::ASTFor(ASTNode *Init, ASTNode *Condition, ASTNode *Increment,
               ASTCompound *Body, unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_FOR_STMT, LineNo, ColumnNo), mInit(Init),
      mCondition(Condition), mIncrement(Increment), mBody(Body) {}

ASTFor::~ASTFor() {
  delete mInit;
  delete mCondition;
  delete mIncrement;
  delete mBody;
}

void ASTFor::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTFor::Init() const { return mInit; }

ASTNode *ASTFor::Condition() const { return mCondition; }

ASTNode *ASTFor::Increment() const { return mIncrement; }

ASTCompound *ASTFor::Body() const { return mBody; }

} // namespace weak