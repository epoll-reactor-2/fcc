/* ASTForStmt.h - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FOR_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FOR_H

#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTFor : public ASTNode {
public:
  ASTFor(ASTNode *Init, ASTNode *Condition, ASTNode *Increment,
         ASTCompound *Body, unsigned LineNo, unsigned ColumnNo);

  ~ASTFor();

  void Accept(ASTVisitor *) override;

  ASTNode *Init() const;
  ASTNode *Condition() const;
  ASTNode *Increment() const;
  ASTCompound *Body() const;

private:
  ASTNode *mInit;
  ASTNode *mCondition;
  ASTNode *mIncrement;
  ASTCompound *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FOR_H