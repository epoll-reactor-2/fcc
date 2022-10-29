/* ASTFloatingPointLiteral.h - AST node to represent a floating point number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FLOATING_POINT_LITERAL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FLOATING_POINT_LITERAL_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTFloatingPointLiteral : public ASTNode {
public:
  ASTFloatingPointLiteral(float TheValue, unsigned TheLineNo = 0U,
                          unsigned TheColumnNo = 0U);

  void Accept(ASTVisitor *) override;

  float GetValue() const;

private:
  float Value;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FLOATING_POINT_LITERAL_H