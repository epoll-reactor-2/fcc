/* ASTWhileStmt.cpp - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTWhileStmt.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTWhileStmt::ASTWhileStmt(ASTNode *TheCondition, ASTCompoundStmt *TheBody,
                           unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Condition(TheCondition), Body(TheBody) {}

ASTWhileStmt::~ASTWhileStmt() {
  delete Condition;
  delete Body;
}

ASTType ASTWhileStmt::GetASTType() const { return AST_WHILE_STMT; }

void ASTWhileStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTWhileStmt::GetCondition() const { return Condition; }

ASTCompoundStmt *ASTWhileStmt::GetBody() const { return Body; }

} // namespace weak