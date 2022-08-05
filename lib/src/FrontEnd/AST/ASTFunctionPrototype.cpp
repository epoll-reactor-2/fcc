/* ASTFunctionPrototype.cpp - AST node to represent a function prototype.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTFunctionPrototype.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"
#include "FrontEnd/Lex/Token.hpp"

namespace weak {
namespace frontEnd {

ASTFunctionPrototype::ASTFunctionPrototype(
    TokenType TheReturnType, std::string &&TheName,
    std::vector<std::unique_ptr<ASTNode>> &&TheArguments, unsigned TheLineNo,
    unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), ReturnType(TheReturnType),
      Name(std::move(TheName)), Arguments(std::move(TheArguments)) {}

ASTType ASTFunctionPrototype::GetASTType() const {
  return ASTType::FUNCTION_PROTOTYPE;
}

void ASTFunctionPrototype::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTFunctionPrototype::GetReturnType() const { return ReturnType; }

const std::string &ASTFunctionPrototype::GetName() const { return Name; }

std::vector<std::unique_ptr<ASTNode>> &&ASTFunctionPrototype::GetArguments() {
  return std::move(Arguments);
}

const std::vector<std::unique_ptr<ASTNode>> &
ASTFunctionPrototype::GetArguments() const {
  return Arguments;
}

} // namespace frontEnd
} // namespace weak