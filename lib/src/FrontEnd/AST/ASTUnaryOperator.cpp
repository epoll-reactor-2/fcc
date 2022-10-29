/* ASTUnaryOperator.cpp - AST node to represent a unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTUnaryOperator.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTUnaryOperator::ASTUnaryOperator(UnaryType PrefixOrPostfix,
                                   TokenType Operation, ASTNode *Operand,
                                   unsigned LineNo, unsigned ColumnNo)
    : ASTNode(
          (PrefixOrPostfix == POSTFIX ? AST_POSTFIX_UNARY : AST_PREFIX_UNARY),
          LineNo, ColumnNo),
      PrefixOrPostfix(PrefixOrPostfix), mOperation(Operation),
      mOperand(Operand) {}

ASTUnaryOperator::~ASTUnaryOperator() { delete mOperand; }

void ASTUnaryOperator::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTUnaryOperator::Operation() const { return mOperation; }

ASTNode *ASTUnaryOperator::Operand() const { return mOperand; }

} // namespace weak