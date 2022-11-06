/* ASTUnaryOperator.h - AST node to represent a unary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_UNARY_H
#define WEAK_COMPILER_FRONTEND_AST_AST_UNARY_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/TokenType.h"

namespace weak {

class ASTUnary : public ASTNode {
public:
  enum UnaryType { PREFIX, POSTFIX } const PrefixOrPostfix;

  ASTUnary(UnaryType PrefixOrPostfix, TokenType Operation, ASTNode *Operand,
           unsigned LineNo, unsigned ColumnNo);

  ~ASTUnary();

  void Accept(ASTVisitor *) override;

  TokenType Operation() const;
  ASTNode *Operand() const;

private:
  TokenType mOperation;
  ASTNode *mOperand;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_UNARY_H