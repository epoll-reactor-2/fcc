/* ASTArrayAccess.h - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H
#define WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H

#include "FrontEnd/AST/ASTNode.h"
#include <string>
#include <vector>

namespace weak {

class ASTArrayAccess : public ASTNode {
public:
  ASTArrayAccess(
    std::string            Name,
    std::vector<ASTNode *> Indices,
    unsigned               TheLineNo,
    unsigned               TheColumnNo
  );

  ~ASTArrayAccess();

  void Accept(ASTVisitor *) override;

  const std::string &Name() const;
  const std::vector<ASTNode *> &Indices() const;

private:
  std::string mName;
  std::vector<ASTNode *> mIndices;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H