/* VariableUseAnalysis.cpp - Semantic analyzer to determine variable issues.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "FrontEnd/AST/AST.h"
#include "Utility/Diagnostic.h"

namespace weak {

static const char *ASTDeclToString(ASTNode *Node) {
  switch (Node->Type()) {
  case AST_FUNCTION_CALL:
  case AST_FUNCTION_DECL:
  case AST_FUNCTION_PROTOTYPE:
    return "Function";
  case AST_VAR_DECL:
  case AST_ARRAY_DECL:
  case AST_ARRAY_ACCESS:
  case AST_SYMBOL:
    return "Variable";
  default:
    Unreachable();
  }
}

VariableUseAnalysis::VariableUseAnalysis(ASTNode *Root)
  : mRoot(Root) {}

void VariableUseAnalysis::Analyze() {
  mRoot->Accept(this);
}

void VariableUseAnalysis::Visit(ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);

  AddUseOnVarAccess(Stmt->LHS());
  AddUseOnVarAccess(Stmt->RHS());
}

void VariableUseAnalysis::Visit(ASTUnary *Stmt) {
  auto *Op = Stmt->Operand();

  bool IsVariable = false;
  IsVariable |= Op->Is(AST_SYMBOL);
  IsVariable |= Op->Is(AST_ARRAY_ACCESS);
  if (!IsVariable)
    weak::CompileError(Stmt)
      << "Variable as argument of unary operator expected";

  Op->Accept(this);
  AddUseOnVarAccess(Op);
}

void VariableUseAnalysis::Visit(ASTFor *Stmt) {
  mStorage.StartScope();

  if (auto *I = Stmt->Init())
    I->Accept(this);

  if (auto *C = Stmt->Condition())
    C->Accept(this);

  if (auto *I = Stmt->Increment())
    I->Accept(this);

  Stmt->Body()->Accept(this);

  MakeUnusedVarAnalysis();

  mStorage.EndScope();
}

void VariableUseAnalysis::Visit(ASTFunctionDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);

  mStorage.StartScope();
  /// This is to have function in recursive calls.
  mStorage.Push(Decl->Name(), Decl);
  for (ASTNode *A : Decl->Args())
    A->Accept(this);

  Decl->Body()->Accept(this);

  MakeUnusedVarAnalysis();

  mStorage.EndScope();
  /// This is to have function outside.
  mStorage.Push(Decl->Name(), Decl);
}

void VariableUseAnalysis::Visit(ASTFunctionCall *Stmt) {
  const auto &Symbol = Stmt->Name();
  AssertIsDeclared(Symbol, Stmt);

  ASTNode *Func = mStorage.Lookup(Symbol)->AST;

  /// Used to handle expressions like that
  /// int value = 0;
  /// value();
  bool IsFunction = false;
  IsFunction |= Func->Is(AST_FUNCTION_DECL);
  IsFunction |= Func->Is(AST_FUNCTION_PROTOTYPE);
  if (!IsFunction)
    weak::CompileError(Stmt) << "`" << Symbol << "` is not a function";

  mStorage.AddUse(Symbol);

  for (ASTNode *A : Stmt->Args())
    A->Accept(this);
}

void VariableUseAnalysis::Visit(ASTFunctionPrototype *Stmt) {
  AssertIsNotDeclared(Stmt->Name(), Stmt);
  mStorage.Push(Stmt->Name(), Stmt);
}

void VariableUseAnalysis::Visit(ASTArrayDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);
  mStorage.Push(Decl->Name(), Decl);
}

void VariableUseAnalysis::Visit(ASTVarDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);
  mStorage.Push(Decl->Name(), Decl);

  if (auto *B = Decl->Body())
    B->Accept(this);
}

void VariableUseAnalysis::Visit(ASTArrayAccess *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
  Stmt->Index()->Accept(this);
  mStorage.AddUse(Stmt->Name());
}

void VariableUseAnalysis::Visit(ASTSymbol *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
  mStorage.AddUse(Stmt->Name());
}

void VariableUseAnalysis::Visit(ASTCompound *Stmt) {
  mStorage.StartScope();
  for (ASTNode *S : Stmt->Stmts())
    S->Accept(this);

  MakeUnusedVarAndFuncAnalysis();

  mStorage.EndScope();
}

void VariableUseAnalysis::Visit(ASTReturn *Stmt) {
  if (auto *O = Stmt->Operand())
    O->Accept(this);
}

void VariableUseAnalysis::Visit(ASTMemberAccess *Stmt) {
  auto *Symbol = static_cast<ASTSymbol *>(Stmt->Name());
  AssertIsDeclared(Symbol->Name(), Stmt);
  mStorage.AddUse(Symbol->Name());
}

void VariableUseAnalysis::AssertIsDeclared(std::string_view Name, ASTNode *AST) {
  if (!mStorage.Lookup(Name))
    weak::CompileError(AST)
      << ASTDeclToString(AST) << " `" << Name << "` not found";
}

void VariableUseAnalysis::AssertIsNotDeclared(std::string_view Name, ASTNode *AST) {
  if (!mStorage.Lookup(Name))
    return;

  auto *Decl = mStorage.Lookup(Name)->AST;
  unsigned LineNo = Decl->LineNo();
  unsigned ColumnNo = Decl->ColumnNo();

  weak::CompileError(AST)
    << ASTDeclToString(AST) << " `" << Name
    << "` already declared at line " << LineNo
    << ", column " << ColumnNo;
}

void VariableUseAnalysis::AddUseOnVarAccess(ASTNode *Stmt) {
  if (Stmt->Is(AST_SYMBOL)) {
    auto *S = static_cast<ASTSymbol *>(Stmt);
    mStorage.AddUse(S->Name());
  }

  if (Stmt->Is(AST_ARRAY_ACCESS)) {
    auto *A = static_cast<ASTArrayAccess *>(Stmt);
    mStorage.AddUse(A->Name());
  }
}

void VariableUseAnalysis::MakeUnusedVarAndFuncAnalysis() {
  for (auto *U : mStorage.CurrScopeUses()) {
    bool IsFunction = false;
    IsFunction |= U->AST->Is(AST_FUNCTION_DECL);
    IsFunction |= U->AST->Is(AST_FUNCTION_PROTOTYPE);
    bool IsMainFunction = false;

    if (IsFunction) {
      auto *Main = static_cast<ASTFunctionDecl *>(U->AST);
      IsMainFunction = Main->Name() == "main";
    }

    if (U->Uses == 0U && !IsMainFunction)
      weak::CompileWarning(U->AST)
        << (IsFunction ? "Function" : "Variable")
        << " `" << U->Name << "` is never used";
  }
}

void VariableUseAnalysis::MakeUnusedVarAnalysis() {
  for (auto *U : mStorage.CurrScopeUses()) {
    bool IsFunction = false;
    IsFunction |= U->AST->Is(AST_FUNCTION_DECL);
    IsFunction |= U->AST->Is(AST_FUNCTION_PROTOTYPE);

    if (U->Uses == 0U && !IsFunction)
      weak::CompileWarning(U->AST)
        << "Variable"
        << " `" << U->Name << "` is never used";
  }
}

} // namespace weak