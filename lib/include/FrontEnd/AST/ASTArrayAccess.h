/* ASTArrayAccess.h - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H
#define WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/Token.h"

namespace weak {

class ASTArrayAccess : public ASTNode {
public:
  ASTArrayAccess(std::string Name, ASTNode *Index, unsigned TheLineNo,
                 unsigned TheColumnNo);

  ~ASTArrayAccess();

  void Accept(ASTVisitor *) override;

  const std::string &Name() const;
  ASTNode *Index() const;

private:
  std::string mName;
  ASTNode *mIndex;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_H