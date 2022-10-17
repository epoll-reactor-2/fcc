/* ASTUnaryOperator.cpp - AST node to represent a unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTUnaryOperator.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTUnaryOperator::ASTUnaryOperator(UnaryType ThePrefixOrPostfix,
                                   TokenType TheOperation,
                                   std::unique_ptr<ASTNode> &&TheOperand,
                                   unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), PrefixOrPostfix(ThePrefixOrPostfix),
      Operation(TheOperation), Operand(std::move(TheOperand)) {}

ASTType ASTUnaryOperator::GetASTType() const {
  return PrefixOrPostfix == UnaryType::POSTFIX ? ASTType::POSTFIX_UNARY
                                               : ASTType::PREFIX_UNARY;
}

void ASTUnaryOperator::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTUnaryOperator::GetOperation() const { return Operation; }

const std::unique_ptr<ASTNode> &ASTUnaryOperator::GetOperand() const {
  return Operand;
}

} // namespace weak