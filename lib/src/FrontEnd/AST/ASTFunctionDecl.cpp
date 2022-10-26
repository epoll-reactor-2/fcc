/* ASTFunctionDecl.cpp - AST node to represent a function itself.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFunctionDecl.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"
#include "FrontEnd/Lex/Token.hpp"

namespace weak {

ASTFunctionDecl::ASTFunctionDecl(TokenType TheReturnType, std::string &&TheName,
                                 std::vector<ASTNode *> &&TheArguments,
                                 ASTCompoundStmt *TheBody, unsigned TheLineNo,
                                 unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), ReturnType(TheReturnType),
      Name(std::move(TheName)), Arguments(std::move(TheArguments)),
      Body(TheBody) {}

ASTFunctionDecl::~ASTFunctionDecl() {
  for (ASTNode *Arg : Arguments)
    delete Arg;
  delete Body;
}

ASTType ASTFunctionDecl::GetASTType() const { return AST_FUNCTION_DECL; }

void ASTFunctionDecl::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTFunctionDecl::GetReturnType() const { return ReturnType; }

const std::string &ASTFunctionDecl::GetName() const { return Name; }

std::vector<ASTNode *> &&ASTFunctionDecl::GetArguments() {
  return std::move(Arguments);
}

const std::vector<ASTNode *> &ASTFunctionDecl::GetArguments() const {
  return Arguments;
}

ASTCompoundStmt *ASTFunctionDecl::GetBody() const { return Body; }

} // namespace weak