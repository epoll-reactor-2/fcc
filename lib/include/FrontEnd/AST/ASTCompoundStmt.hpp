/* ASTCompoundStmt.hpp - AST node to represent a block of code.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_STMT_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_STMT_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include <memory>
#include <vector>

namespace weak {

class ASTCompoundStmt : public ASTNode {
public:
  ASTCompoundStmt(std::vector<std::unique_ptr<ASTNode>> &&stmts,
                  unsigned TheLineNo = 0U, unsigned TheColumnNo = 0U);

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  std::vector<std::unique_ptr<ASTNode>> &&GetStmts();
  const std::vector<std::unique_ptr<ASTNode>> &GetStmts() const;

private:
  std::vector<std::unique_ptr<ASTNode>> Stmts;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_COMPOUND_STMT_HPP