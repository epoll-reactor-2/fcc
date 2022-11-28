/* ASTUnary.cpp - AST node to represent a unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTUnary.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTUnary::ASTUnary(
  UnaryType  PrefixOrPostfix,
  TokenType  Operation,
  ASTNode   *Operand,
  unsigned   LineNo,
  unsigned   ColumnNo
) : ASTNode(
      PrefixOrPostfix == POSTFIX
        ? AST_POSTFIX_UNARY
        : AST_PREFIX_UNARY,
      LineNo, ColumnNo)
  , PrefixOrPostfix(PrefixOrPostfix)
  , mOperation(Operation)
  , mOperand(Operand) {}

ASTUnary::~ASTUnary() {
  delete mOperand;
}

void ASTUnary::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

TokenType ASTUnary::Operation() const {
  return mOperation;
}

ASTNode *ASTUnary::Operand() const {
  return mOperand;
}

} // namespace weak