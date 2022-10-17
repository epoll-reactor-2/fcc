/* ASTForStmt.cpp - AST node to represent a for statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTForStmt.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTForStmt::ASTForStmt(std::unique_ptr<ASTNode> &&TheInit,
                       std::unique_ptr<ASTNode> &&TheCondition,
                       std::unique_ptr<ASTNode> &&TheIncrement,
                       std::unique_ptr<ASTCompoundStmt> &&TheBody,
                       unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Init(std::move(TheInit)),
      Condition(std::move(TheCondition)), Increment(std::move(TheIncrement)),
      Body(std::move(TheBody)) {}

ASTType ASTForStmt::GetASTType() const { return ASTType::FOR_STMT; }

void ASTForStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

std::unique_ptr<ASTNode> &&ASTForStmt::GetInit() { return std::move(Init); }

const std::unique_ptr<ASTNode> &ASTForStmt::GetInit() const { return Init; }

std::unique_ptr<ASTNode> &&ASTForStmt::GetCondition() {
  return std::move(Condition);
}

const std::unique_ptr<ASTNode> &ASTForStmt::GetCondition() const {
  return Condition;
}

std::unique_ptr<ASTNode> &&ASTForStmt::GetIncrement() {
  return std::move(Increment);
}

const std::unique_ptr<ASTNode> &ASTForStmt::GetIncrement() const {
  return Increment;
}

std::unique_ptr<ASTCompoundStmt> &&ASTForStmt::GetBody() {
  return std::move(Body);
}

const std::unique_ptr<ASTCompoundStmt> &ASTForStmt::GetBody() const {
  return Body;
}

} // namespace weak