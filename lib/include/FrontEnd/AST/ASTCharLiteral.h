/* ASTCharLiteral.h - AST node to represent a single character.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_CHAR_LITERAL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_CHAR_LITERAL_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTCharLiteral : public ASTNode {
public:
  ASTCharLiteral(char TheValue, unsigned TheLineNo = 0U,
                 unsigned TheColumnNo = 0U);

  void Accept(ASTVisitor *) override;

  char GetValue() const;

private:
  char Value;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_CHAR_LITERAL_H