/* ASTDoWhileStmt.cpp - AST node to represent a do-while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTDoWhileStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTDoWhileStmt::ASTDoWhileStmt(ASTCompoundStmt *TheBody, ASTNode *TheCondition,
                               unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_DO_WHILE_STMT, TheLineNo, TheColumnNo), Body(TheBody),
      Condition(TheCondition) {}

ASTDoWhileStmt::~ASTDoWhileStmt() {
  delete Body;
  delete Condition;
}

void ASTDoWhileStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTCompoundStmt *ASTDoWhileStmt::GetBody() const { return std::move(Body); }

ASTNode *ASTDoWhileStmt::GetCondition() const { return Condition; }

} // namespace weak