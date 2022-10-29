/* ASTBinaryOperator.cpp - AST node to represent a binary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBinaryOperator.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTBinaryOperator::ASTBinaryOperator(TokenType Operation, ASTNode *LHS,
                                     ASTNode *RHS, unsigned LineNo,
                                     unsigned ColumnNo)
    : ASTNode(AST_BINARY, LineNo, ColumnNo), mOperation(Operation), mLHS(LHS),
      mRHS(RHS) {}

ASTBinaryOperator::~ASTBinaryOperator() {
  delete mLHS;
  delete mRHS;
}

void ASTBinaryOperator::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTBinaryOperator::Operation() const { return mOperation; }

ASTNode *ASTBinaryOperator::LHS() const { return mLHS; }
ASTNode *ASTBinaryOperator::RHS() const { return mRHS; }

} // namespace weak