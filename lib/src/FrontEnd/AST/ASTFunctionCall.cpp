/* ASTFunctionCall.cpp - AST node to represent a function call statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFunctionCall.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTFunctionCall::ASTFunctionCall(std::string &&Name,
                                 std::vector<ASTNode *> &&Arguments,
                                 unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_FUNCTION_CALL, LineNo, ColumnNo), mName(std::move(Name)),
      mArgs(std::move(Arguments)) {}

ASTFunctionCall::~ASTFunctionCall() {
  for (ASTNode *Arg : mArgs)
    delete Arg;
}

void ASTFunctionCall::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTFunctionCall::Name() const { return mName; }

const std::vector<ASTNode *> &ASTFunctionCall::Args() const { return mArgs; }

} // namespace weak