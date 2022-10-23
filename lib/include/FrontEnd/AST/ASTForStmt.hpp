/* ASTForStmt.hpp - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FOR_STMT_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_FOR_STMT_HPP

#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/AST/ASTNode.hpp"

namespace weak {

class ASTForStmt : public ASTNode {
public:
  ASTForStmt(ASTNode *TheInit, ASTNode *TheCondition, ASTNode *TheIncrement,
             ASTCompoundStmt *TheBody, unsigned TheLineNo = 0U,
             unsigned TheColumnNo = 0U);

  ~ASTForStmt();

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  ASTNode *GetInit() const;
  ASTNode *GetCondition() const;
  ASTNode *GetIncrement() const;
  ASTCompoundStmt *GetBody() const;

private:
  ASTNode *Init;
  ASTNode *Condition;
  ASTNode *Increment;
  ASTCompoundStmt *Body;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FOR_STMT_HPP