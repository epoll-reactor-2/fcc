/* ASTVarDecl.cpp - AST node to represent a variable declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTVarDecl::ASTVarDecl(
  weak::DataType  DT,
  std::string     Name,
  ASTNode        *Body,
  unsigned        LineNo,
  unsigned        ColumnNo
) : ASTNode(AST_VAR_DECL, LineNo, ColumnNo)
  , mDataType(DT)
  , mTypeName("")
  , mName(std::move(Name))
  , mBody(Body) {}

ASTVarDecl::ASTVarDecl(
  weak::DataType  DT,
  std::string     TypeName,
  std::string     Name,
  ASTNode        *Body,
  unsigned        LineNo,
  unsigned        ColumnNo
) : ASTNode(AST_VAR_DECL, LineNo, ColumnNo)
  , mDataType(DT)
  , mTypeName(std::move(TypeName))
  , mName(std::move(Name))
  , mBody(Body) {}

ASTVarDecl::~ASTVarDecl() {
  delete mBody;
}

void ASTVarDecl::Accept(ASTVisitor *Visitor) {
  Visitor->Visit(this);
}

weak::DataType ASTVarDecl::DataType() const {
  return mDataType;
}

const std::string &ASTVarDecl::Name() const {
  return mName;
}

const std::string &ASTVarDecl::TypeName() const {
  return mTypeName;
}

ASTNode *ASTVarDecl::Body() const {
  return mBody;
}

} // namespace weak