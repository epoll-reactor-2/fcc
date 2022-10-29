/* ASTBooleanLiteral.h - AST node to represent a boolean literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_BOOLEAN_LITERAL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_BOOLEAN_LITERAL_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTBooleanLiteral : public ASTNode {
public:
  ASTBooleanLiteral(bool TheValue, unsigned TheLineNo = 0U,
                    unsigned TheColumnNo = 0U);

  void Accept(ASTVisitor *) override;

  bool GetValue() const;

private:
  bool Value;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_BOOLEAN_LITERAL_H