/* ASTReturnStmt.cpp - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTReturnStmt.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTReturnStmt::ASTReturnStmt(ASTNode *Operand, unsigned LineNo,
                             unsigned ColumnNo)
    : ASTNode(AST_RETURN_STMT, LineNo, ColumnNo), mOperand(Operand) {}

ASTReturnStmt::~ASTReturnStmt() { delete mOperand; }

void ASTReturnStmt::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTReturnStmt::Operand() const { return mOperand; }

} // namespace weak