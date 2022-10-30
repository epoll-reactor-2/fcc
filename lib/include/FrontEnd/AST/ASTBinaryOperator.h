/* ASTBinaryOperator.h - AST node to represent a binary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BINARY_OPERATOR_H
#define WEAK_COMPILER_FRONTEND_AST_AST_BINARY_OPERATOR_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/Token.h"

namespace weak {

class ASTBinaryOperator : public ASTNode {
public:
  ASTBinaryOperator(TokenType Operation, ASTNode *LHS, ASTNode *RHS,
                    unsigned LineNo, unsigned ColumnNo);

  ~ASTBinaryOperator();

  void Accept(ASTVisitor *) override;

  TokenType Operation() const;
  ASTNode *LHS() const;
  ASTNode *RHS() const;

private:
  TokenType mOperation;
  ASTNode *mLHS;
  ASTNode *mRHS;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BINARY_OPERATOR_H