/* ASTNode.h - Basic AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_NODE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_NODE_H

#include "FrontEnd/AST/ASTType.h"

namespace weak {

class ASTVisitor;

class ASTNode {
public:
  virtual ~ASTNode() = default;
  virtual void Accept(ASTVisitor *) = 0;

  ASTType Type() const;
  bool Is(ASTType) const;

  unsigned LineNo() const;
  unsigned ColumnNo() const;

protected:
  ASTNode(ASTType Type, unsigned LineNo, unsigned ColumnNo);

  ASTType mType;
  unsigned mLineNo;
  unsigned mColumnNo;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_NODE_H