/* ASTUnaryOperator.cpp - AST node to represent a unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTUnaryOperator.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTUnaryOperator::ASTUnaryOperator(UnaryType ThePrefixOrPostfix,
                                   TokenType TheOperation, ASTNode *TheOperand,
                                   unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode((ThePrefixOrPostfix == POSTFIX ? AST_POSTFIX_UNARY
                                             : AST_PREFIX_UNARY),
              TheLineNo, TheColumnNo),
      PrefixOrPostfix(ThePrefixOrPostfix), Operation(TheOperation),
      Operand(TheOperand) {}

ASTUnaryOperator::~ASTUnaryOperator() { delete Operand; }

void ASTUnaryOperator::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTUnaryOperator::GetOperation() const { return Operation; }

ASTNode *ASTUnaryOperator::GetOperand() const { return Operand; }

} // namespace weak