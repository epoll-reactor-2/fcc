/* ASTBinaryOperator.h - AST node to represent a binary operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BINARY_H
#define WEAK_COMPILER_FRONTEND_AST_AST_BINARY_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/TokenType.h"

namespace weak {

class ASTBinary : public ASTNode {
public:
  ASTBinary(TokenType Operation, ASTNode *LHS, ASTNode *RHS, unsigned LineNo,
            unsigned ColumnNo);

  ~ASTBinary();

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

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BINARY_H