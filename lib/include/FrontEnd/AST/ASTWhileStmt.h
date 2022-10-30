/* ASTWhileStmt.h - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_WHILE_STMT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_WHILE_STMT_H

#include "FrontEnd/AST/ASTCompoundStmt.h"
#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTWhileStmt : public ASTNode {
public:
  ASTWhileStmt(ASTNode *Condition, ASTCompoundStmt *Body,
               unsigned LineNo, unsigned ColumnNo);

  ~ASTWhileStmt();

  void Accept(ASTVisitor *) override;

  ASTNode *Condition() const;
  ASTCompoundStmt *Body() const;

private:
  ASTNode *mCondition;
  ASTCompoundStmt *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_WHILE_STMT_H