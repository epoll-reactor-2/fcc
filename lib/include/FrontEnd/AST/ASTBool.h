/* ASTBooleanLiteral.h - AST node to represent a boolean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BOOL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_BOOL_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTBool : public ASTNode {
public:
  ASTBool(bool Value, unsigned LineNo, unsigned ColumnNo);

  void Accept(ASTVisitor *) override;

  bool Value() const;

private:
  bool mValue;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BOOL_H