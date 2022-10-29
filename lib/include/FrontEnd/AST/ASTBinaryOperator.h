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
  ASTBinaryOperator(TokenType TheOperation, ASTNode *TheLHS, ASTNode *TheRHS,
                    unsigned TheLineNo = 0U, unsigned TheColumnNo = 0U);

  ~ASTBinaryOperator();

  void Accept(ASTVisitor *) override;

  TokenType GetOperation() const;
  ASTNode *GetLHS() const;
  ASTNode *GetRHS() const;

private:
  TokenType Operation;
  ASTNode *LHS;
  ASTNode *RHS;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BINARY_OPERATOR_H