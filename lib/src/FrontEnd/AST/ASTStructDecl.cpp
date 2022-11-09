/* ASTStructDecl.cpp - AST node to represent a type declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTStructDecl.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTStructDecl::ASTStructDecl(std::string Name, std::vector<ASTNode *> Decls,
                             unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_STRUCT_DECL, LineNo, ColumnNo), mName(std::move(Name)),
      mDecls(std::move(Decls)) {}

ASTStructDecl::~ASTStructDecl() {
  for (ASTNode *D : mDecls)
    delete D;
}

void ASTStructDecl::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::vector<ASTNode *> &ASTStructDecl::Decls() const { return mDecls; }

const std::string &ASTStructDecl::Name() const { return mName; }

} // namespace weak