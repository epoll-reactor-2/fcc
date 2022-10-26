/* ASTFunctionCall.cpp - AST node to represent a function call statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFunctionCall.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTFunctionCall::ASTFunctionCall(std::string &&TheName,
                                 std::vector<ASTNode *> &&TheArguments,
                                 unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_FUNCTION_CALL, TheLineNo, TheColumnNo),
      Name(std::move(TheName)), Arguments(std::move(TheArguments)) {}

ASTFunctionCall::~ASTFunctionCall() {
  for (ASTNode *Arg : Arguments)
    delete Arg;
}

void ASTFunctionCall::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::string &ASTFunctionCall::GetName() const { return Name; }

const std::vector<ASTNode *> &ASTFunctionCall::GetArguments() const {
  return Arguments;
}

} // namespace weak