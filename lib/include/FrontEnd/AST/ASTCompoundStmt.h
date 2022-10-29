/* ASTCompoundStmt.h - AST node to represent a block of code.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_STMT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_STMT_H

#include "FrontEnd/AST/ASTNode.h"
#include <vector>

namespace weak {

class ASTCompoundStmt : public ASTNode {
public:
  ASTCompoundStmt(std::vector<ASTNode *> &&TheStmts, unsigned TheLineNo = 0U,
                  unsigned TheColumnNo = 0U);

  ~ASTCompoundStmt();

  void Accept(ASTVisitor *) override;

  const std::vector<ASTNode *> &GetStmts() const;

private:
  std::vector<ASTNode *> Stmts;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_STMT_H