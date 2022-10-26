/* ASTBinaryOperator.hpp - AST node to represent a binary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BINARY_OPERATOR_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_BINARY_OPERATOR_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/Lex/Token.hpp"

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

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BINARY_OPERATOR_HPP