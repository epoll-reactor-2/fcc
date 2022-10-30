/* ASTForStmt.h - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FOR_STMT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FOR_STMT_H

#include "FrontEnd/AST/ASTCompoundStmt.h"
#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTForStmt : public ASTNode {
public:
  ASTForStmt(ASTNode *Init, ASTNode *Condition, ASTNode *Increment,
             ASTCompoundStmt *Body, unsigned LineNo,
             unsigned ColumnNo);

  ~ASTForStmt();

  void Accept(ASTVisitor *) override;

  ASTNode *Init() const;
  ASTNode *Condition() const;
  ASTNode *Increment() const;
  ASTCompoundStmt *Body() const;

private:
  ASTNode *mInit;
  ASTNode *mCondition;
  ASTNode *mIncrement;
  ASTCompoundStmt *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FOR_STMT_H