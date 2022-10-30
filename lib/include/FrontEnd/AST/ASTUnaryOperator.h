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

  ASTUnaryOperator(UnaryType PrefixOrPostfix, TokenType Operation,
                   ASTNode *Operand, unsigned LineNo,
                   unsigned ColumnNo);

  ~ASTUnaryOperator();

  void Accept(ASTVisitor *) override;

  TokenType Operation() const;
  ASTNode *Operand() const;

private:
  TokenType mOperation;
  ASTNode *mOperand;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_UNARY_OPERATOR_H