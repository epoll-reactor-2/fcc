/* ASTStructDecl.h - AST node to represent a type declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_H

#include "FrontEnd/AST/ASTNode.h"
#include <string>
#include <vector>

namespace weak {

class ASTStructDecl : public ASTNode {
public:
  /// Consequense of LLVM IR backend. It requires
  /// indices of struct fields in order to access them.
  struct IndexedDeclaration {
    ASTNode *Decl;
    unsigned Idx;
  };

  ASTStructDecl(
    std::string                     Name,
    std::vector<IndexedDeclaration> Decls,
    unsigned                        LineNo,
    unsigned                        ColumnNo
  );

  ~ASTStructDecl();

  void Accept(ASTVisitor *) override;

  const std::vector<IndexedDeclaration> &Decls() const;
  const std::string &Name() const;

private:
  std::string mName;
  std::vector<IndexedDeclaration> mDecls;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_DECL_H