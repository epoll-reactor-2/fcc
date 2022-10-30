/* ASTStringLiteral.h - AST node to represent a string literal.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_STRING_LITERAL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_STRING_LITERAL_H

#include "FrontEnd/AST/ASTNode.h"
#include <string>

namespace weak {

class ASTStringLiteral : public ASTNode {
public:
  ASTStringLiteral(std::string Value, unsigned LineNo,
                   unsigned ColumnNo);

  void Accept(ASTVisitor *) override;

  const std::string &Value() const;

private:
  std::string mValue;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_STRING_LITERAL_H