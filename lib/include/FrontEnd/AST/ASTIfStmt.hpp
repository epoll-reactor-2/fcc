/* ASTIfStmt.hpp - AST node to represent a if or if-else statements.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_IF_STMT_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_IF_STMT_HPP

#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/AST/ASTNode.hpp"

namespace weak {

class ASTIfStmt : public ASTNode {
public:
  ASTIfStmt(ASTNode *TheCondition, ASTCompoundStmt *TheThenBody,
            ASTCompoundStmt *TheElseBody, unsigned TheLineNo = 0U,
            unsigned TheColumnNo = 0U);

  ~ASTIfStmt();

  ASTType GetASTType() const override;
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

#endif // WEAK_COMPILER_FRONTEND_AST_AST_IF_STMT_HPP