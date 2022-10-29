/* ASTWhileStmt.cpp - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTWhileStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTWhileStmt::ASTWhileStmt(ASTNode *TheCondition, ASTCompoundStmt *TheBody,
                           unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_WHILE_STMT, TheLineNo, TheColumnNo), Condition(TheCondition),
      Body(TheBody) {}

ASTWhileStmt::~ASTWhileStmt() {
  delete Condition;
  delete Body;
}

void ASTWhileStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTWhileStmt::GetCondition() const { return Condition; }

ASTCompoundStmt *ASTWhileStmt::GetBody() const { return Body; }

} // namespace weak