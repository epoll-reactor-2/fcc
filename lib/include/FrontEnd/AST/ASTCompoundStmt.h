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
  ASTCompoundStmt(std::vector<ASTNode *> &&Stmts, unsigned LineNo,
                  unsigned ColumnNo);

  ~ASTCompoundStmt();

  void Accept(ASTVisitor *) override;

  const std::vector<ASTNode *> &Stmts() const;

private:
  std::vector<ASTNode *> mStmts;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_STMT_H