/* ASTBinaryOperator.cpp - AST node to represent a binary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBinary.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTBinary::ASTBinary(TokenType Operation, ASTNode *LHS, ASTNode *RHS,
                     unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_BINARY, LineNo, ColumnNo), mOperation(Operation), mLHS(LHS),
      mRHS(RHS) {}

ASTBinary::~ASTBinary() {
  delete mLHS;
  delete mRHS;
}

void ASTBinary::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTBinary::Operation() const { return mOperation; }

ASTNode *ASTBinary::LHS() const { return mLHS; }
ASTNode *ASTBinary::RHS() const { return mRHS; }

} // namespace weak