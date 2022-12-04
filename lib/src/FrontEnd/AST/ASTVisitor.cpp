/* ASTVisitor.cpp - Common-use class to traverse the AST.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTVisitor.h"
#include "FrontEnd/AST/ASTArrayAccess.h"
#include "FrontEnd/AST/ASTBinary.h"
#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTDoWhile.h"
#include "FrontEnd/AST/ASTFor.h"
#include "FrontEnd/AST/ASTFunctionCall.h"
#include "FrontEnd/AST/ASTFunctionDecl.h"
#include "FrontEnd/AST/ASTFunctionPrototype.h"
#include "FrontEnd/AST/ASTIf.h"
#include "FrontEnd/AST/ASTMemberAccess.h"
#include "FrontEnd/AST/ASTReturn.h"
#include "FrontEnd/AST/ASTStructDecl.h"
#include "FrontEnd/AST/ASTSymbol.h"
#include "FrontEnd/AST/ASTUnary.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/AST/ASTWhile.h"

namespace weak {

void ASTVisitor::Visit(ASTArrayAccess *Stmt) {
  for (auto *I : Stmt->Indices())
    I->Accept(this);
}

void ASTVisitor::Visit(ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);
}

void ASTVisitor::Visit(ASTCompound *Stmt) {
  for (auto *S : Stmt->Stmts())
    S->Accept(this);
}

void ASTVisitor::Visit(ASTDoWhile *Stmt) {
  Stmt->Body()->Accept(this);
  Stmt->Condition()->Accept(this);
}

void ASTVisitor::Visit(ASTFor *Stmt) {
  if (auto *I = Stmt->Init())
    I->Accept(this);

  if (auto *C = Stmt->Condition())
    C->Accept(this);

  if (auto *I = Stmt->Increment())
    I->Accept(this);

  Stmt->Body()->Accept(this);
}

void ASTVisitor::Visit(ASTFunctionDecl *Decl) {
  for (auto *A : Decl->Args())
    A->Accept(this);
  Decl->Body()->Accept(this);
}

void ASTVisitor::Visit(ASTFunctionCall *Stmt) {
  for (auto *A : Stmt->Args())
    A->Accept(this);
}

void ASTVisitor::Visit(ASTFunctionPrototype *Stmt) {
  for (auto *A : Stmt->Args())
    A->Accept(this);
}

void ASTVisitor::Visit(ASTIf *Stmt) {
  Stmt->Condition()->Accept(this);
  Stmt->ThenBody()->Accept(this);

  if (auto *E = Stmt->ElseBody())
    E->Accept(this);
}

void ASTVisitor::Visit(ASTReturn *Stmt) {
  if (auto *O = Stmt->Operand())
    O->Accept(this);
}

void ASTVisitor::Visit(ASTStructDecl *Decl) {
  for (auto *D : Decl->Decls())
    D->Accept(this);
}

void ASTVisitor::Visit(ASTMemberAccess *Stmt) {
  Stmt->Name()->Accept(this);
  Stmt->MemberDecl()->Accept(this);
}

void ASTVisitor::Visit(ASTUnary *Stmt) {
  Stmt->Operand()->Accept(this);
}

void ASTVisitor::Visit(ASTVarDecl *Decl) {
  if (auto *B = Decl->Body())
    B->Accept(this);
}

void ASTVisitor::Visit(ASTWhile *Stmt) {
  Stmt->Condition()->Accept(this);
  Stmt->Body()->Accept(this);
}

} // namespace weak