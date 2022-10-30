/* ASTSymbol.h - AST node to represent a variable name.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_SYMBOL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_SYMBOL_H

#include "FrontEnd/AST/ASTNode.h"
#include <string>

namespace weak {

class ASTSymbol : public ASTNode {
public:
  ASTSymbol(std::string Value, unsigned LineNo, unsigned ColumnNo);

  void Accept(ASTVisitor *) override;

  const std::string &Name() const;

private:
  std::string mValue;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_SYMBOL_H