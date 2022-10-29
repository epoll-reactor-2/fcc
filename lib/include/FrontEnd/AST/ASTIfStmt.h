/* ASTIfStmt.h - AST node to represent a if or if-else statements.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_IF_STMT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_IF_STMT_H

#include "FrontEnd/AST/ASTCompoundStmt.h"
#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTIfStmt : public ASTNode {
public:
  ASTIfStmt(ASTNode *TheCondition, ASTCompoundStmt *TheThenBody,
            ASTCompoundStmt *TheElseBody, unsigned TheLineNo = 0U,
            unsigned TheColumnNo = 0U);

  ~ASTIfStmt();

  void Accept(ASTVisitor *) override;

  ASTNode *GetCondition() const;
  ASTCompoundStmt *GetThenBody() const;
  ASTCompoundStmt *GetElseBody() const;

private:
  ASTNode *Condition;
  ASTCompoundStmt *ThenBody;
  ASTCompoundStmt *ElseBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_IF_STMT_H