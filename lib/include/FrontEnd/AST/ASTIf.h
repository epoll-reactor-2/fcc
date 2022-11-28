/* ASTIfStmt.h - AST node to represent a if or if-else statements.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_IF_H
#define WEAK_COMPILER_FRONTEND_AST_AST_IF_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTCompound;

class ASTIf : public ASTNode {
public:
  ASTIf(
    ASTNode     *Condition,
    ASTCompound *ThenBody,
    ASTCompound *ElseBody,
    unsigned     LineNo,
    unsigned     ColumnNo
  );

  ~ASTIf();

  void Accept(ASTVisitor *) override;

  ASTNode *Condition() const;
  ASTCompound *ThenBody() const;
  ASTCompound *ElseBody() const;

private:
  ASTNode *mCondition;
  ASTCompound *mThenBody;
  ASTCompound *mElseBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_IF_H