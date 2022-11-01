/* ASTWhileStmt.cpp - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTVisitor.h"
#include "FrontEnd/AST/ASTWhile.h"

namespace weak {

ASTWhile::ASTWhile(ASTNode *Condition, ASTCompound *Body, unsigned LineNo,
                   unsigned ColumnNo)
    : ASTNode(AST_WHILE_STMT, LineNo, ColumnNo), mCondition(Condition),
      mBody(Body) {}

ASTWhile::~ASTWhile() {
  delete mCondition;
  delete mBody;
}

void ASTWhile::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTWhile::Condition() const { return mCondition; }

ASTCompound *ASTWhile::Body() const { return mBody; }

} // namespace weak