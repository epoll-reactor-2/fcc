/* DeadCodeAnalysis.cpp - Unreachable code detector.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/DeadCodeAnalysis.h"
#include "FrontEnd/AST/ASTArrayDecl.h"
#include "FrontEnd/AST/ASTBinary.h"
#include "FrontEnd/AST/ASTBool.h"
#include "FrontEnd/AST/ASTBreak.h"
#include "FrontEnd/AST/ASTDoWhile.h"
#include "FrontEnd/AST/ASTFor.h"
#include "FrontEnd/AST/ASTFunctionDecl.h"
#include "FrontEnd/AST/ASTIf.h"
#include "FrontEnd/AST/ASTNumber.h"
#include "FrontEnd/AST/ASTReturn.h"
#include "FrontEnd/AST/ASTSymbol.h"
#include "FrontEnd/AST/ASTUnary.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/AST/ASTWhile.h"
#include "Utility/Diagnostic.h"
#include <cassert>

namespace weak {

DeadCodeAnalysis::DeadCodeAnalysis(ASTNode *Root) : mRoot(Root) {}

void DeadCodeAnalysis::Analyze() { mRoot->Accept(this); }

void DeadCodeAnalysis::Visit(const ASTBreak *Stmt) {
  mStorage.Push("break", Stmt);
  mShouldAnalyzeLoopConditions = true;
}

void DeadCodeAnalysis::Visit(const ASTReturn *Stmt) {
  mStorage.Push("return", Stmt);
  mShouldAnalyzeLoopConditions = true;
}

void DeadCodeAnalysis::AddUseForVariable(std::string_view Name,
                                         bool AddMutableUse) {
  /// Increment variable use counter if it present in collected
  /// ones, otherwise push new record with use = 0.
  for (auto &Uses : mCollectedUses)
    for (auto UseIt = Uses.begin(); UseIt != Uses.end();)
      if (auto &Use = *UseIt; Use.Name == Name) {
        ++Use.Uses;
        if (AddMutableUse)
          ++Use.MutableUses;
        ++UseIt;
      } else
        UseIt = Uses.emplace(Uses.end(), *mStorage.Lookup(Name));
}

void DeadCodeAnalysis::Visit(const ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);

  switch (Stmt->Operation()) {
  case TOK_ASSIGN:
  case TOK_MUL_ASSIGN:
  case TOK_DIV_ASSIGN:
  case TOK_PLUS_ASSIGN:
  case TOK_MINUS_ASSIGN:
  case TOK_MOD_ASSIGN:
  case TOK_SHL_ASSIGN:
  case TOK_SHR_ASSIGN:
  case TOK_BIT_AND_ASSIGN:
  case TOK_BIT_OR_ASSIGN:
  case TOK_XOR_ASSIGN: {
    /// Assignment statement always requires variable name as
    /// left operand.
    auto *Variable = static_cast<const ASTSymbol *>(Stmt->LHS());
    AddUseForVariable(Variable->Name(), /*AddMutableUse=*/true);
    mShouldAnalyzeLoopConditions = true;
  }
  default:
    break;
  }
}

void DeadCodeAnalysis::Visit(const ASTUnary *Stmt) {
  Stmt->Operand()->Accept(this);

  if (!Stmt->Operand()->Is(AST_SYMBOL))
    return;

  auto *Variable = static_cast<const ASTSymbol *>(Stmt->Operand());

  switch (Stmt->Operation()) {
  case TOK_INC:
  case TOK_DEC: {
    AddUseForVariable(Variable->Name(), /*AddMutableUse=*/true);
    mShouldAnalyzeLoopConditions = true;
  }
  default:
    break;
  }
}

void DeadCodeAnalysis::Visit(const ASTCompound *Stmt) {
  mCollectedUses.push_back(UseStorage{});

  for (auto *S : Stmt->Stmts())
    S->Accept(this);

  if (Stmt->Stmts().empty())
    mShouldAnalyzeLoopConditions = true;

  mCollectedUses.pop_back();
}

void DeadCodeAnalysis::Visit(const ASTArrayDecl *Decl) {
  mStorage.Push(Decl->Name(), Decl);
}

void DeadCodeAnalysis::Visit(const ASTVarDecl *Decl) {
  mStorage.Push(Decl->Name(), Decl);

  if (auto *B = Decl->Body())
    B->Accept(this);
}

void DeadCodeAnalysis::Visit(const ASTFunctionDecl *Decl) {
  mStorage.StartScope();
  for (auto *A : Decl->Args())
    A->Accept(this);
  Decl->Body()->Accept(this);
  mStorage.EndScope();
}

void DeadCodeAnalysis::Visit(const ASTSymbol *Stmt) {
  AddUseForVariable(Stmt->Name(), /*AddMutableUse=*/false);
  mShouldAnalyzeLoopConditions = false;
}

void DeadCodeAnalysis::Visit(const ASTIf *Stmt) {
  bool InvariableCondDetected = false;
  AlwaysTrueOrFalseCheck(Stmt->Condition(), InvariableCondDetected);

  if (!InvariableCondDetected)
    Stmt->Condition()->Accept(this);

  Stmt->ThenBody()->Accept(this);

  if (auto *E = Stmt->ElseBody())
    E->Accept(this);
}

void DeadCodeAnalysis::Visit(const ASTFor *Stmt) {
  mCollectedUses.push_back(UseStorage{});

  if (auto *I = Stmt->Init())
    I->Accept(this);

  auto *Cond = Stmt->Condition();

  /// Note: increment is accepted inside function below.
  if (Cond)
    RunLoopAnalysis(Cond, Stmt->Body(), Stmt->Increment());

  mCollectedUses.pop_back();
}

void DeadCodeAnalysis::Visit(const ASTWhile *Stmt) {
  mCollectedUses.push_back(UseStorage{});
  RunLoopAnalysis(Stmt->Condition(), Stmt->Body());
  mCollectedUses.pop_back();
}

void DeadCodeAnalysis::Visit(const ASTDoWhile *Stmt) {
  mCollectedUses.push_back(UseStorage{});
  RunLoopAnalysis(Stmt->Condition(), Stmt->Body());
  mCollectedUses.pop_back();
}

void DeadCodeAnalysis::RunLoopAnalysis(ASTNode *Condition, ASTNode *Body,
                                       ASTNode *ForIncrement) {
  mStorage.StartScope();

  Condition->Accept(this);

  assert(!mCollectedUses.empty());
  /// We are interested only in last set of uses only
  /// from condition.
  auto CondUses = mCollectedUses.back();

  bool InvariableCondDetected = false;
  AlwaysTrueOrFalseCheck(Condition, InvariableCondDetected);

  Body->Accept(this);

  if (ForIncrement)
    ForIncrement->Accept(this);

  if (InvariableCondDetected || !mShouldAnalyzeLoopConditions)
    return;

  const auto &BodyUses = mCollectedUses;

  bool CommonUses = false;

  for (auto &CondUse : CondUses)
    for (auto &BodyUseEntry : BodyUses)
      for (auto &BodyUse : BodyUseEntry)
        CommonUses |=
            ((CondUse.Name == BodyUse.Name) && BodyUse.MutableUses > 0);

  bool ShouldWarn = true;
  ShouldWarn &= !CommonUses;
  ShouldWarn &= (!mStorage.Lookup("break") && !mStorage.Lookup("return"));

  if (ShouldWarn)
    /// No one variable from condition was changed in loop body as well as
    /// there is no `break` or `return` statements, so we can assume, that
    /// it is infinite loop.
    weak::CompileWarning(Condition) << "Condition is never changed";

  mStorage.EndScope();
}

void DeadCodeAnalysis::AlwaysTrueOrFalseCheck(const ASTNode *Stmt,
                                              bool &WasChecked) {
  if (mStorage.Lookup("break") || mStorage.Lookup("return"))
    return;

  if (Stmt->Is(AST_BOOLEAN_LITERAL)) {
    auto *Bool = static_cast<const ASTBool *>(Stmt);
    weak::CompileWarning(Bool)
        << "Condition " << (Bool->Value() ? "always" : "never")
        << " evaluates to true";
    WasChecked = true;
  }

  if (Stmt->Is(AST_INTEGER_LITERAL)) {
    auto *Num = static_cast<const ASTNumber *>(Stmt);
    weak::CompileWarning(Num)
        << "Condition " << (Num->Value() != 0 ? "always" : "never")
        << " evaluates to true";
    WasChecked = true;
  }
}

} // namespace weak