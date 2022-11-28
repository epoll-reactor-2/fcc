/* ASTWhileStmt.h - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_WHILE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_WHILE_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTCompound;

class ASTWhile : public ASTNode {
public:
  ASTWhile(
    ASTNode     *Condition,
    ASTCompound *Body,
    unsigned     LineNo,
    unsigned     ColumnNo
  );

  ~ASTWhile();

  void Accept(ASTVisitor *) override;

  ASTNode *Condition() const;
  ASTCompound *Body() const;

private:
  ASTNode *mCondition;
  ASTCompound *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_WHILE_H