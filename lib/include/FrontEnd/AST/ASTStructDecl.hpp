/* ASTStructDecl.hpp - AST node to represent a type declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include <string>
#include <vector>

namespace weak {

class ASTStructDecl : public ASTNode {
public:
  ASTStructDecl(std::string TheName, std::vector<ASTNode *> TheDecls,
                unsigned TheLineNo = 0U, unsigned TheColumnNo = 0U);

  ~ASTStructDecl();

  void Accept(ASTVisitor *) override;

  const std::vector<ASTNode *> &GetDecls() const;
  const std::string &GetName() const;

private:
  std::string Name;
  std::vector<ASTNode *> Decls;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_HPP