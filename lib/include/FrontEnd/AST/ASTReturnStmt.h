/* ASTReturnStmt.h - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_RETURN_STMT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_RETURN_STMT_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTReturnStmt : public ASTNode {
public:
  ASTReturnStmt(ASTNode *Operand, unsigned LineNo = 0U,
                unsigned ColumnNo = 0U);

  ~ASTReturnStmt();

  void Accept(ASTVisitor *) override;

  ASTNode *Operand() const;

private:
  ASTNode *mOperand;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_RETURN_STMT_H