/* ASTDoWhileStmt.cpp - AST node to represent a do-while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTDoWhileStmt.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTDoWhileStmt::ASTDoWhileStmt(ASTCompoundStmt *TheBody, ASTNode *TheCondition,
                               unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Body(TheBody), Condition(TheCondition) {}

ASTDoWhileStmt::~ASTDoWhileStmt() {
  delete Body;
  delete Condition;
}

ASTType ASTDoWhileStmt::GetASTType() const { return AST_DO_WHILE_STMT; }

void ASTDoWhileStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTCompoundStmt *ASTDoWhileStmt::GetBody() const { return std::move(Body); }

ASTNode *ASTDoWhileStmt::GetCondition() const { return Condition; }

} // namespace weak