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
#include "FrontEnd/AST/ASTReturn.h"
#include "FrontEnd/AST/ASTStructDecl.h"
#include "FrontEnd/AST/ASTUnary.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/AST/ASTWhile.h"

namespace weak {

void ASTVisitor::Visit(const ASTArrayAccess *Stmt) {
  Stmt->Index()->Accept(this);
}

void ASTVisitor::Visit(const ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);
}

void ASTVisitor::Visit(const ASTCompound *Stmt) {
  for (auto *S : Stmt->Stmts())
    S->Accept(this);
}

void ASTVisitor::Visit(const ASTDoWhile *Stmt) {
  Stmt->Body()->Accept(this);
  Stmt->Condition()->Accept(this);
}

void ASTVisitor::Visit(const ASTFor *Stmt) {
  if (auto *I = Stmt->Init())
    I->Accept(this);

  if (auto *C = Stmt->Condition())
    C->Accept(this);

  if (auto *I = Stmt->Increment())
    I->Accept(this);

  Stmt->Body()->Accept(this);
}

void ASTVisitor::Visit(const ASTFunctionDecl *Decl) {
  for (auto *A : Decl->Args())
    A->Accept(this);
  Decl->Body()->Accept(this);
}

void ASTVisitor::Visit(const ASTFunctionCall *Stmt) {
  for (auto *A : Stmt->Args())
    A->Accept(this);
}

void ASTVisitor::Visit(const ASTFunctionPrototype *Stmt) {
  for (auto *A : Stmt->Args())
    A->Accept(this);
}

void ASTVisitor::Visit(const ASTIf *Stmt) {
  Stmt->Condition()->Accept(this);
  Stmt->ThenBody()->Accept(this);

  if (auto *E = Stmt->ElseBody())
    E->Accept(this);
}

void ASTVisitor::Visit(const ASTReturn *Stmt) {
  printf("ASTVisitor::Return\n");
  if (auto *O = Stmt->Operand())
    O->Accept(this);
}

void ASTVisitor::Visit(const ASTStructDecl *Decl) {
  for (auto *D : Decl->Decls())
    D->Accept(this);
}

void ASTVisitor::Visit(const ASTUnary *Stmt) { Stmt->Operand()->Accept(this); }

void ASTVisitor::Visit(const ASTVarDecl *Decl) { Decl->Body()->Accept(this); }

void ASTVisitor::Visit(const ASTWhile *Stmt) {
  Stmt->Condition()->Accept(this);
  Stmt->Body()->Accept(this);
}

} // namespace weak