/* ASTNode.hpp - Basic AST node.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_NODE_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_NODE_HPP

#include "FrontEnd/AST/ASTTypesEnum.hpp"

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

#endif // WEAK_COMPILER_FRONTEND_AST_AST_NODE_HPP