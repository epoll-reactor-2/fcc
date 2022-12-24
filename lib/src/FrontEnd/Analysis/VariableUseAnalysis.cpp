/* VariableUseAnalysis.cpp - Semantic analyzer to determine variable issues.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/VariableUseAnalysis.h"
#include "FrontEnd/AST/AST.h"
#include "FrontEnd/Lex/Token.h"
#include "Utility/Diagnostic.h"
#include "Utility/Unreachable.h"

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
    Unreachable("Expected variable or function AST.");
  }
}

VariableUseAnalysis::VariableUseAnalysis(ASTNode *Root)
  : mRoot(Root) {
  mCollectedNodes.push_back({});
}

void VariableUseAnalysis::Analyze() {
  mRoot->Accept(this);
}

void VariableUseAnalysis::Visit(ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);

  if (Stmt->Operation() == TOK_ASSIGN)
    AddWriteUse(Stmt->LHS());
  else
    AddReadUse(Stmt->LHS());
  AddReadUse(Stmt->RHS());
}

void VariableUseAnalysis::Visit(ASTUnary *Stmt) {
  auto *Op = Stmt->Operand();

  bool IsVariable = false;
  IsVariable |= Op->Is(AST_SYMBOL);
  IsVariable |= Op->Is(AST_ARRAY_ACCESS);
  IsVariable |= Op->Is(AST_MEMBER_ACCESS);
  IsVariable |= Op->Is(AST_BINARY);
  IsVariable |= Op->Is(AST_PREFIX_UNARY);
  IsVariable |= Op->Is(AST_POSTFIX_UNARY);
  if (!IsVariable)
    weak::CompileError(Stmt)
      << "Variable as argument of unary operator expected";

  Op->Accept(this);
  /// Since there are only `++` and `--` operators in language
  /// they are both writable.
  AddWriteUse(Op);
}

void VariableUseAnalysis::Visit(ASTFor *Stmt) {
  mStorage.StartScope();

  if (auto *I = Stmt->Init())
    I->Accept(this);

  if (auto *C = Stmt->Condition()) {
    mCollectedNodes.push_back({});
    C->Accept(this);
    for (ASTNode *Node : mCollectedNodes.back())
      AddReadUse(Node);
    mCollectedNodes.pop_back();
  }

  if (auto *I = Stmt->Increment())
    I->Accept(this);

  Stmt->Body()->Accept(this);

  UnusedVarAnalysis();

  mStorage.EndScope();
}

void VariableUseAnalysis::Visit(ASTWhile *Stmt) {
  mCollectedNodes.push_back({});
  Stmt->Condition()->Accept(this);
  for (ASTNode *Node : mCollectedNodes.back())
    AddReadUse(Node);
  mCollectedNodes.pop_back();
  Stmt->Body()->Accept(this);
}

void VariableUseAnalysis::Visit(ASTDoWhile *Stmt) {
  mCollectedNodes.push_back({});
  Stmt->Condition()->Accept(this);
  for (ASTNode *Node : mCollectedNodes.back())
    AddReadUse(Node);
  mCollectedNodes.pop_back();
  Stmt->Body()->Accept(this);
}

void VariableUseAnalysis::Visit(ASTFunctionDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);

  mStorage.StartScope();
  /// This is to have function in recursive calls.
  mStorage.Push(Decl->Name(), Decl);
  for (ASTNode *A : Decl->Args())
    A->Accept(this);

  Decl->Body()->Accept(this);

  UnusedVarAnalysis();
  mStorage.EndScope();
  /// This is to have function outside.
  mStorage.Push(Decl->Name(), Decl);
}

void VariableUseAnalysis::Visit(ASTFunctionCall *Stmt) {
  const auto &FunctionName = Stmt->Name();
  AssertIsDeclared(FunctionName, Stmt);

  ASTNode *Func = mStorage.Lookup(FunctionName)->AST;

  /// Used to handle expressions like that
  /// int value = 0;
  /// value();
  bool IsFunction = false;
  IsFunction |= Func->Is(AST_FUNCTION_DECL);
  IsFunction |= Func->Is(AST_FUNCTION_PROTOTYPE);
  if (!IsFunction)
    weak::CompileError(Stmt) << "`" << FunctionName << "` is not a function";

  mStorage.AddReadUse(FunctionName);

  for (ASTNode *Arg : Stmt->Args()) {
    Arg->Accept(this);
    AddReadUse(Arg);
  }
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
  mCollectedNodes.back().push_back(Stmt);
  for (auto *I : Stmt->Indices())
    I->Accept(this);
  /// We will decide if there is write use of this statement
  /// inside binary/unary operators logic.
}

void VariableUseAnalysis::Visit(ASTSymbol *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
  mCollectedNodes.back().push_back(Stmt);
  /// We will decide if there is write use of this statement
  /// inside binary/unary operators logic.
}

void VariableUseAnalysis::Visit(ASTMemberAccess *Stmt) {
//  auto *Symbol = static_cast<ASTSymbol *>(Stmt->Name());
//  AssertIsDeclared(Symbol->Name(), Stmt);
  mCollectedNodes.back().push_back(Stmt);
}

void VariableUseAnalysis::Visit(ASTCompound *Stmt) {
  mStorage.StartScope();
  for (ASTNode *Stmt : Stmt->Stmts())
    Stmt->Accept(this);

  UnusedVarAndFuncAnalysis();
  mStorage.EndScope();
}

void VariableUseAnalysis::Visit(ASTReturn *Stmt) {
  if (auto *O = Stmt->Operand()) {
    O->Accept(this);
    AddReadUse(O);
  }
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

void VariableUseAnalysis::AddReadUse(ASTNode *Stmt) {
  if (Stmt->Is(AST_SYMBOL)) {
    auto *S = static_cast<ASTSymbol *>(Stmt);
    mStorage.AddReadUse(S->Name());
  }

  if (Stmt->Is(AST_ARRAY_ACCESS)) {
    auto *A = static_cast<ASTArrayAccess *>(Stmt);
    mStorage.AddReadUse(A->Name());
  }

  if (Stmt->Is(AST_MEMBER_ACCESS)) {
    auto *M = static_cast<ASTMemberAccess *>(Stmt);
    if (M->Name()->Is(AST_SYMBOL)) {
      auto *S = static_cast<ASTSymbol *>(M->Name());
      mStorage.AddReadUse(S->Name());
    }
  }
}

void VariableUseAnalysis::AddWriteUse(ASTNode *Stmt) {
  if (Stmt->Is(AST_SYMBOL)) {
    auto *S = static_cast<ASTSymbol *>(Stmt);
    mStorage.AddWriteUse(S->Name());
  }

  if (Stmt->Is(AST_ARRAY_ACCESS)) {
    auto *A = static_cast<ASTArrayAccess *>(Stmt);
    mStorage.AddWriteUse(A->Name());
  }

  if (Stmt->Is(AST_MEMBER_ACCESS)) {
    auto *M = static_cast<ASTMemberAccess *>(Stmt);
    if (M->Name()->Is(AST_SYMBOL)) {
      auto *S = static_cast<ASTSymbol *>(M->Name());
      mStorage.AddWriteUse(S->Name());
    }
  }
}

void VariableUseAnalysis::UnusedVarAndFuncAnalysis() {
  for (auto *Use : mStorage.CurrScopeUses()) {
    bool IsFunction = false;
    IsFunction |= Use->AST->Is(AST_FUNCTION_DECL);
    IsFunction |= Use->AST->Is(AST_FUNCTION_PROTOTYPE);
    bool IsMainFunction = false;

    if (IsFunction) {
      auto *Main = static_cast<ASTFunctionDecl *>(Use->AST);
      IsMainFunction = Main->Name() == "main";
    }

    if (!IsMainFunction && Use->ReadUses == 0U)
      weak::CompileWarning(Use->AST)
        << (IsFunction ? "Function" : "Variable")
        << " `" << Use->Name << "` "
        << (Use->WriteUses
           ? "written, but never read"
           : "is never used");
  }
}

void VariableUseAnalysis::UnusedVarAnalysis() {
  for (auto *Use : mStorage.CurrScopeUses()) {
    bool IsFunction = false;
    IsFunction |= Use->AST->Is(AST_FUNCTION_DECL);
    IsFunction |= Use->AST->Is(AST_FUNCTION_PROTOTYPE);

    if (!IsFunction && Use->ReadUses == 0U)
      weak::CompileWarning(Use->AST)
        << "Variable `" << Use->Name << "` "
        << (Use->WriteUses
           ? "written, but never read"
           : "is never used");
  }
}

} // namespace weak