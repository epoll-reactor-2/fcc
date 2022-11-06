/* ASTContinue.cpp - AST node to represent a continue statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTContinue.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTContinue::ASTContinue(unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_CONTINUE_STMT, LineNo, ColumnNo) {}

void ASTContinue::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

} // namespace weak