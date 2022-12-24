/* ASTMemberAccess.cpp - AST node to represent a field access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTMemberAccess.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTMemberAccess::ASTMemberAccess(
  ASTNode  *Name,
  ASTNode  *MemberDecl,
  unsigned  LineNo,
  unsigned  ColumnNo
) : ASTNode(AST_MEMBER_ACCESS, LineNo, ColumnNo)
  , mName(Name)
  , mMemberDecl(MemberDecl) {}

ASTMemberAccess::~ASTMemberAccess() {
  delete mName;
  delete mMemberDecl;
}

void ASTMemberAccess::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

ASTNode *ASTMemberAccess::Name() const {
  return mName;
}

ASTNode *ASTMemberAccess::MemberDecl() const {
  return mMemberDecl;
}

} // namespace weak