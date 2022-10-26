/* ASTBreakStmt.cpp - AST node to represent a break statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBreakStmt.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTBreakStmt::ASTBreakStmt(unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo) {}

ASTType ASTBreakStmt::GetASTType() const { return AST_BREAK_STMT; }

void ASTBreakStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

} // namespace weak