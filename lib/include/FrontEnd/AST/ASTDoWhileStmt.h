/* ASTDoWhileStmt.h - AST node to represent a do-while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_DO_WHILE_STMT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_DO_WHILE_STMT_H

#include "FrontEnd/AST/ASTCompoundStmt.h"
#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTDoWhileStmt : public ASTNode {
public:
  ASTDoWhileStmt(ASTCompoundStmt *Body, ASTNode *Condition,
                 unsigned LineNo, unsigned ColumnNo);

  ~ASTDoWhileStmt();

  void Accept(ASTVisitor *) override;

  ASTCompoundStmt *Body() const;
  ASTNode *Condition() const;

private:
  ASTCompoundStmt *mBody;
  ASTNode *mCondition;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_DO_WHILE_STMT_H