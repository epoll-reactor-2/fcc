/* ASTBreakStmt.cpp - AST node to represent a break statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTBreak.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTBreak::ASTBreak(unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_BREAK_STMT, LineNo, ColumnNo) {}

void ASTBreak::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

} // namespace weak