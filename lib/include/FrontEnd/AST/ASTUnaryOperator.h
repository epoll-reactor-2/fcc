/* ASTUnaryOperator.h - AST node to represent a unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_UNARY_OPERATOR_H
#define WEAK_COMPILER_FRONTEND_AST_AST_UNARY_OPERATOR_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/Token.h"

namespace weak {

class ASTUnaryOperator : public ASTNode {
public:
  enum UnaryType { PREFIX, POSTFIX } const PrefixOrPostfix;

  ASTUnaryOperator(UnaryType ThePrefixOrPostfix, TokenType TheOperation,
                   ASTNode *TheOperand, unsigned TheLineNo = 0U,
                   unsigned TheColumnNo = 0U);

  ~ASTUnaryOperator();

  void Accept(ASTVisitor *) override;

  TokenType GetOperation() const;
  ASTNode *GetOperand() const;

private:
  TokenType Operation;
  ASTNode *Operand;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_UNARY_OPERATOR_H