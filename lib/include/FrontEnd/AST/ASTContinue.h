/* ASTContinueStmt.h - AST node to represent a continue statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_CONTINUE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_CONTINUE_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTContinue : public ASTNode {
public:
  ASTContinue(unsigned LineNo, unsigned ColumnNo);

  void Accept(ASTVisitor *) override;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_CONTINUE_H