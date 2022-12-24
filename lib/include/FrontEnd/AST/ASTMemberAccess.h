/* ASTMemberAccess.h - AST node to represent a field access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_FIELD_ACCESS_H
#define WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_FIELD_ACCESS_H

#include "FrontEnd/AST/ASTNode.h"
#include <string>
#include <vector>

namespace weak {

class ASTSymbol;

class ASTMemberAccess : public ASTNode {
public:
  ASTMemberAccess(
    ASTNode  *Name,
    ASTNode  *MemberDecl,
    unsigned  LineNo,
    unsigned  ColumnNo
  );

  ~ASTMemberAccess();

  void Accept(ASTVisitor *) override;

  ASTNode *Name() const;
  ASTNode *MemberDecl() const;

private:
  ASTNode *mName;
  ASTNode *mMemberDecl;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_STRUCT_FIELD_ACCESS_H