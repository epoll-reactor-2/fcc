/* ASTForStmt.cpp - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTForStmt.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTForStmt::ASTForStmt(ASTNode *TheInit, ASTNode *TheCondition,
                       ASTNode *TheIncrement, ASTCompoundStmt *TheBody,
                       unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_FOR_STMT, TheLineNo, TheColumnNo), Init(TheInit),
      Condition(TheCondition), Increment(TheIncrement), Body(TheBody) {}

ASTForStmt::~ASTForStmt() {
  delete Init;
  delete Condition;
  delete Increment;
  delete Body;
}

void ASTForStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTForStmt::GetInit() const { return Init; }

ASTNode *ASTForStmt::GetCondition() const { return Condition; }

ASTNode *ASTForStmt::GetIncrement() const { return Increment; }

ASTCompoundStmt *ASTForStmt::GetBody() const { return Body; }

} // namespace weak