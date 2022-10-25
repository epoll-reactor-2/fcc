/* ASTStructDecl.cpp - AST node to represent a type declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTStructDecl.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTStructDecl::ASTStructDecl(std::string TheName,
                             std::vector<ASTNode *> TheDecls,
                             unsigned int TheLineNo, unsigned int TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Name(std::move(TheName)),
      Decls(std::move(TheDecls)) {}

ASTStructDecl::~ASTStructDecl() {
  for (ASTNode *D : Decls)
    delete D;
}

ASTType ASTStructDecl::GetASTType() const { return ASTType::SYMBOL; }

void ASTStructDecl::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::vector<ASTNode *> &ASTStructDecl::GetDecls() const { return Decls; }

const std::string &ASTStructDecl::GetName() const { return Name; }

} // namespace weak