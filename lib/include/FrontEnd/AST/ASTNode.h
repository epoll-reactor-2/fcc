/* ASTNode.h - Basic AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_NODE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_NODE_H

#include "FrontEnd/AST/ASTTypesEnum.h"

namespace weak {

class ASTVisitor;

class ASTNode {
public:
  virtual ~ASTNode() = default;
  virtual void Accept(ASTVisitor *) = 0;

  ASTType GetASTType() const;
  bool Is(ASTType) const;

  unsigned GetLineNo() const;
  unsigned GetColumnNo() const;

protected:
  ASTNode(ASTType TheType, unsigned TheLineNo, unsigned TheColumnNo);

  ASTType Type;
  unsigned LineNo;
  unsigned ColumnNo;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_NODE_H