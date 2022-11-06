/* ASTIf.cpp - AST node to represent a if or if-else statements.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTIf.h"
#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTIf::ASTIf(ASTNode *Condition, ASTCompound *ThenBody, ASTCompound *ElseBody,
             unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_IF_STMT, LineNo, ColumnNo), mCondition(Condition),
      mThenBody(ThenBody), mElseBody(ElseBody) {}

ASTIf::~ASTIf() {
  delete mCondition;
  delete mThenBody;
  delete mElseBody;
}

void ASTIf::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTIf::Condition() const { return mCondition; }

ASTCompound *ASTIf::ThenBody() const { return mThenBody; }

ASTCompound *ASTIf::ElseBody() const { return mElseBody; }

} // namespace weak