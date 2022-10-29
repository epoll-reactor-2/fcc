/* ASTBreakStmt.cpp - AST node to represent a break statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBreakStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTBreakStmt::ASTBreakStmt(unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_BREAK_STMT, LineNo, ColumnNo) {}

void ASTBreakStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

} // namespace weak