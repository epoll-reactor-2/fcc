/* ASTFloatingPointLiteral.h - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FLOAT_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FLOAT_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTFloat : public ASTNode {
public:
  ASTFloat(float Value, unsigned LineNo, unsigned ColumnNo);

  void Accept(ASTVisitor *) override;

  float Value() const;

private:
  float mValue;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FLOAT_H