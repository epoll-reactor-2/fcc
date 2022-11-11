/* ASTFunctionPrototype.cpp - AST node to represent a function prototype.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFunctionPrototype.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTFunctionPrototype::ASTFunctionPrototype(DataType ReturnType,
                                           std::string Name,
                                           std::vector<ASTNode *> Args,
                                           unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_FUNCTION_PROTOTYPE, LineNo, ColumnNo),
      mReturnType(ReturnType), mName(std::move(Name)), mArgs(std::move(Args)) {}

ASTFunctionPrototype::~ASTFunctionPrototype() {
  for (ASTNode *Arg : mArgs)
    delete Arg;
}

void ASTFunctionPrototype::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

DataType ASTFunctionPrototype::ReturnType() const { return mReturnType; }

const std::string &ASTFunctionPrototype::Name() const { return mName; }

const std::vector<ASTNode *> &ASTFunctionPrototype::Args() const {
  return mArgs;
}

} // namespace weak