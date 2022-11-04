/* VariableUseAnalysis.cpp - Semantic analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "FrontEnd/AST/AST.h"
#include "Utility/Diagnostic.h"
#include <algorithm>

namespace weak {

VariableUseAnalysis::VariableUseAnalysis(ASTNode *Root) : mRoot(Root) {}

void VariableUseAnalysis::AssertIsDeclared(std::string_view Name,
                                           const ASTNode *InformAST) {
  if (!mStorage.Lookup(Name))
    weak::CompileError(InformAST)
        << (InformAST->Is(AST_FUNCTION_CALL) ? "Function" : "Variable") << " `"
        << Name << "` not found";
}

void VariableUseAnalysis::AssertIsNotDeclared(std::string_view Name,
                                              const ASTNode *InformAST) {
  if (mStorage.Lookup(Name))
    weak::CompileError(InformAST)
        << (InformAST->Is(AST_FUNCTION_CALL) ? "Function" : "Variable") << " `"
        << Name << "` already declared";
}

void VariableUseAnalysis::Analyze() { mRoot->Accept(this); }

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

void VariableUseAnalysis::Visit(const ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);

  AddUseOnVarAccess(Stmt->LHS());
  AddUseOnVarAccess(Stmt->RHS());
}

void VariableUseAnalysis::Visit(const ASTUnary *Stmt) {
  if (auto *Op = Stmt->Operand();
      !Op->Is(AST_SYMBOL) && !Op->Is(AST_ARRAY_ACCESS))
    weak::CompileError(Stmt)
        << "Variable as argument of unary operator expected";

  Stmt->Operand()->Accept(this);

  AddUseOnVarAccess(Stmt->Operand());
}

void VariableUseAnalysis::Visit(const ASTFor *Stmt) {
  mStorage.StartScope();

  if (auto *I = Stmt->Init())
    I->Accept(this);

  if (auto *C = Stmt->Condition())
    C->Accept(this);

  if (auto *I = Stmt->Increment())
    I->Accept(this);

  Stmt->Body()->Accept(this);

  mStorage.EndScope();
}

void VariableUseAnalysis::Visit(const ASTFunctionDecl *Decl) {
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

void VariableUseAnalysis::Visit(const ASTFunctionCall *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);

  const ASTNode *Func = mStorage.Lookup(Stmt->Name())->Value;

  /// Used to handle expressions like that
  /// int value = 0;
  /// value();
  if (!Func->Is(AST_FUNCTION_DECL) && !Func->Is(AST_FUNCTION_PROTOTYPE))
    weak::CompileError(Stmt) << "`" << Stmt->Name() << "` is not a function";

  mStorage.AddUse(Stmt->Name());

  for (ASTNode *A : Stmt->Args())
    A->Accept(this);
}

void VariableUseAnalysis::Visit(const ASTFunctionPrototype *Stmt) {
  AssertIsNotDeclared(Stmt->Name(), Stmt);

  for (ASTNode *A : Stmt->Args())
    A->Accept(this);

  mStorage.Push(Stmt->Name(), Stmt);
}

void VariableUseAnalysis::Visit(const ASTArrayDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);
  mStorage.Push(Decl->Name(), Decl);
}

void VariableUseAnalysis::Visit(const ASTVarDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);
  mStorage.Push(Decl->Name(), Decl);
}

void VariableUseAnalysis::Visit(const ASTArrayAccess *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
  mStorage.AddUse(Stmt->Name());
}

void VariableUseAnalysis::Visit(const ASTSymbol *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
  mStorage.AddUse(Stmt->Name());
}

void VariableUseAnalysis::Visit(const ASTCompound *Stmt) {
  mStorage.StartScope();
  for (ASTNode *S : Stmt->Stmts())
    S->Accept(this);

  MakeUnusedVarAndFuncAnalysis();

  mStorage.EndScope();
}

void VariableUseAnalysis::Visit(const ASTReturn *Stmt) {
  if (auto *O = Stmt->Operand())
    O->Accept(this);
}

void VariableUseAnalysis::MakeUnusedVarAndFuncAnalysis() {
  for (auto *U : mStorage.CurrScopeUses()) {
    bool IsFunction = U->Value->Is(AST_FUNCTION_DECL);
    bool IsMainFunction = false;

    if (IsFunction)
      IsMainFunction =
          static_cast<const ASTFunctionDecl *>(U->Value)->Name() == "main";

    if (U->Uses == 0 && !IsMainFunction)
      weak::CompileWarning(U->Value) << (IsFunction ? "Function" : "Variable")
                                     << " `" << U->Name << "` is never used";
  }
}

void VariableUseAnalysis::MakeUnusedVarAnalysis() {
  for (auto *U : mStorage.CurrScopeUses()) {
    bool IsFunction = U->Value->Is(AST_FUNCTION_DECL);

    if (U->Uses == 0 && !IsFunction)
      weak::CompileWarning(U->Value) << "Variable"
                                     << " `" << U->Name << "` is never used";
  }
}

} // namespace weak
