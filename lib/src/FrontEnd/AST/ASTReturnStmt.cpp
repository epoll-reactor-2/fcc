/* ASTReturnStmt.cpp - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTReturnStmt.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {
namespace frontEnd {

ASTReturnStmt::ASTReturnStmt(std::unique_ptr<ASTNode> &&TheOperand,
                             unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), Operand(std::move(TheOperand)) {}

ASTType ASTReturnStmt::GetASTType() const { return ASTType::RETURN_STMT; }

void ASTReturnStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

const std::unique_ptr<ASTNode> &ASTReturnStmt::GetOperand() const {
  return Operand;
}

} // namespace frontEnd
} // namespace weak