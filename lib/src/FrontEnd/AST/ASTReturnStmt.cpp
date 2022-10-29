/* ASTReturnStmt.cpp - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTReturnStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTReturnStmt::ASTReturnStmt(ASTNode *TheOperand, unsigned TheLineNo,
                             unsigned TheColumnNo)
    : ASTNode(AST_RETURN_STMT, TheLineNo, TheColumnNo), Operand(TheOperand) {}

ASTReturnStmt::~ASTReturnStmt() { delete Operand; }

void ASTReturnStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTReturnStmt::GetOperand() const { return Operand; }

} // namespace weak