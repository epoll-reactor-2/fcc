/* ASTContinueStmt.cpp - AST node to represent a continue statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTContinueStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTContinueStmt::ASTContinueStmt(unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(AST_CONTINUE_STMT, TheLineNo, TheColumnNo) {}

void ASTContinueStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

} // namespace weak