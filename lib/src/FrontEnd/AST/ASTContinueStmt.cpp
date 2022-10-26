/* ASTContinueStmt.cpp - AST node to represent a continue statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTContinueStmt.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTContinueStmt::ASTContinueStmt(unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo) {}

ASTType ASTContinueStmt::GetASTType() const { return AST_CONTINUE_STMT; }

void ASTContinueStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

} // namespace weak