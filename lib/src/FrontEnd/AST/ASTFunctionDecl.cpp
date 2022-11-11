/* ASTFunctionDecl.cpp - AST node to represent a function itself.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFunctionDecl.h"
#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTVisitor.h"
#include "FrontEnd/Lex/Token.h"

namespace weak {

ASTFunctionDecl::ASTFunctionDecl(DataType ReturnType, std::string Name,
                                 std::vector<ASTNode *> Args, ASTCompound *Body,
                                 unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_FUNCTION_DECL, LineNo, ColumnNo), mReturnType(ReturnType),
      mName(std::move(Name)), mArgs(std::move(Args)), mBody(Body) {}

ASTFunctionDecl::~ASTFunctionDecl() {
  for (ASTNode *Arg : mArgs)
    delete Arg;
  delete mBody;
}

void ASTFunctionDecl::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

DataType ASTFunctionDecl::ReturnType() const { return mReturnType; }

const std::string &ASTFunctionDecl::Name() const { return mName; }

const std::vector<ASTNode *> &ASTFunctionDecl::Args() const { return mArgs; }

ASTCompound *ASTFunctionDecl::Body() const { return mBody; }

} // namespace weak