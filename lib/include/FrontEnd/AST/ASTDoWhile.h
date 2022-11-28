/* ASTDoWhileStmt.h - AST node to represent a do-while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_DO_WHILE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_DO_WHILE_H

#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTDoWhile : public ASTNode {
public:
  ASTDoWhile(
    ASTCompound *Body,
    ASTNode     *Condition,
    unsigned     LineNo,
    unsigned     ColumnNo
  );

  ~ASTDoWhile();

  void Accept(ASTVisitor *) override;

  ASTCompound *Body() const;
  ASTNode *Condition() const;

private:
  ASTCompound *mBody;
  ASTNode *mCondition;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_DO_WHILE_H