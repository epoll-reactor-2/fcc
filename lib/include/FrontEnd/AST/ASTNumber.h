/* ASTIntegerLiteral.h - AST node to represent a integer number.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_NUMBER_H
#define WEAK_COMPILER_FRONTEND_AST_AST_NUMBER_H

#include "FrontEnd/AST/ASTNode.h"

namespace weak {

class ASTNumber : public ASTNode {
public:
  ASTNumber(signed Value, unsigned LineNo, unsigned ColumnNo);

  void Accept(ASTVisitor *) override;

  signed Value() const;

private:
  signed mValue;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_NUMBER_H