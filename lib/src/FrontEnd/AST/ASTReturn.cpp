/* ASTReturn.cpp - AST node to represent a return statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTReturn.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTReturn::ASTReturn(ASTNode *Operand, unsigned LineNo, unsigned ColumnNo)
    : ASTNode(AST_RETURN_STMT, LineNo, ColumnNo), mOperand(Operand) {}

ASTReturn::~ASTReturn() { delete mOperand; }

void ASTReturn::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

ASTNode *ASTReturn::Operand() const { return mOperand; }

} // namespace weak