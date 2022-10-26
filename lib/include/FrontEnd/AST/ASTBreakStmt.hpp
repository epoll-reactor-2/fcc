/* ASTBreakStmt.hpp - AST node to represent a break statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BREAK_STMT_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_BREAK_STMT_HPP

#include "FrontEnd/AST/ASTNode.hpp"

namespace weak {

class ASTBreakStmt : public ASTNode {
public:
  ASTBreakStmt(unsigned TheLineNo = 0U, unsigned TheColumnNo = 0U);

  void Accept(ASTVisitor *) override;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BREAK_STMT_HPP