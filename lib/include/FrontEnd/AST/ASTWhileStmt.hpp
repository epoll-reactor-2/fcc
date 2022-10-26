/* ASTWhileStmt.hpp - AST node to represent a while statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_WHILE_STMT_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_WHILE_STMT_HPP

#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/AST/ASTNode.hpp"

namespace weak {

class ASTWhileStmt : public ASTNode {
public:
  ASTWhileStmt(ASTNode *TheCondition, ASTCompoundStmt *TheBody,
               unsigned TheLineNo = 0U, unsigned TheColumnNo = 0U);

  ~ASTWhileStmt();

  void Accept(ASTVisitor *) override;

  ASTNode *GetCondition() const;
  ASTCompoundStmt *GetBody() const;

private:
  ASTNode *Condition;
  ASTCompoundStmt *Body;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_WHILE_STMT_HPP