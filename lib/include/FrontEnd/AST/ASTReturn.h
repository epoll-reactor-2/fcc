/* ASTReturnStmt.h - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_RETURN_H
#define WEAK_COMPILER_FRONTEND_AST_AST_RETURN_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTReturn : public ASTNode {
public:
  ASTReturn(ASTNode *Operand, unsigned LineNo, unsigned ColumnNo);

  ~ASTReturn();

  void Accept(ASTVisitor *) override;

  ASTNode *Operand() const;

private:
  ASTNode *mOperand;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_RETURN_H