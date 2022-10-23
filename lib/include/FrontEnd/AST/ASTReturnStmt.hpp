/* ASTReturnStmt.hpp - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_RETURN_STMT_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_RETURN_STMT_HPP

#include "FrontEnd/AST/ASTNode.hpp"

namespace weak {

class ASTReturnStmt : public ASTNode {
public:
  ASTReturnStmt(ASTNode *TheOperand, unsigned TheLineNo = 0U,
                unsigned TheColumnNo = 0U);

  ~ASTReturnStmt();

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  ASTNode *GetOperand() const;

private:
  ASTNode *Operand;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_RETURN_STMT_HPP