/* DeadCodeAnalysis.cpp - Unreachable code detector.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/DeadCodeAnalysis.h"
#include "FrontEnd/AST/ASTArrayDecl.h"
#include "FrontEnd/AST/ASTBool.h"
#include "FrontEnd/AST/ASTBreak.h"
#include "FrontEnd/AST/ASTDoWhile.h"
#include "FrontEnd/AST/ASTFor.h"
#include "FrontEnd/AST/ASTNumber.h"
#include "FrontEnd/AST/ASTReturn.h"
#include "FrontEnd/AST/ASTSymbol.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/AST/ASTWhile.h"
#include "Utility/Diagnostic.h"
#include <algorithm>

namespace weak {

DeadCodeAnalysis::DeadCodeAnalysis(ASTNode *Root) : mRoot(Root) {}

void DeadCodeAnalysis::Analyze() { mRoot->Accept(this); }

void DeadCodeAnalysis::Visit(const ASTBreak *Stmt) {
  mStorage.Push("break", Stmt);
  ShouldAnalyzeLoopConditions = true;
}

void DeadCodeAnalysis::Visit(const ASTReturn *Stmt) {
  mStorage.Push("return", Stmt);
  ShouldAnalyzeLoopConditions = true;
}

void DeadCodeAnalysis::Visit(const ASTArrayDecl *Decl) {
  mStorage.Push(Decl->Name(), Decl);
}

void DeadCodeAnalysis::Visit(const ASTVarDecl *Decl) {
  mStorage.Push(Decl->Name(), Decl);

  if (auto *B = Decl->Body())
    B->Accept(this);
}

void DeadCodeAnalysis::Visit(const ASTSymbol *Stmt) {
  auto It = std::find_if(
      mCollectedUses.begin(), mCollectedUses.end(),
      [&](ASTStorage::Declaration &Decl) { return Decl.Name == Stmt->Name(); });

  if (It == mCollectedUses.end())
    It = mCollectedUses.emplace(mCollectedUses.end(),
                                *mStorage.Lookup(Stmt->Name()));

  ++It->Uses;

  ShouldAnalyzeLoopConditions = true;
}

void DeadCodeAnalysis::Visit(const ASTFor *) {}

void DeadCodeAnalysis::Visit(const ASTWhile *Stmt) {
  mStorage.StartScope();

  mCollectedUses.clear();
  Stmt->Condition()->Accept(this);
  auto CondUses = mCollectedUses;

  Stmt->Body()->Accept(this);

  bool InfiniteLoopDetected = false;
  InfiniteLoopCheck(Stmt->Condition(), InfiniteLoopDetected);

  auto BodyUses = mCollectedUses;

  unsigned CondUsesSize = CondUses.size();
  unsigned CondAndBodyUsesSize{0U};

  for (const auto &Decl : CondUses) {
    if (auto It = std::find_if(BodyUses.begin(), BodyUses.end(),
                               [&Decl](const ASTStorage::Declaration &D) {
                                 return Decl.Name == D.Name;
                               });
        It != BodyUses.end()) {
      /// Check if variable was not modified in body.
      /// If was modified, add 0, otherwise add 1.
      CondAndBodyUsesSize += Decl.Uses == (*It).Uses;
    }
  }

  if (!InfiniteLoopDetected && ShouldAnalyzeLoopConditions &&
      CondUsesSize == CondAndBodyUsesSize)
    /// No one variable from condition was changed in loop body as well as
    /// there is no `break` or `return` statements, so we can assume, that
    /// it is infinite loop.
    weak::CompileWarning(Stmt->Condition()) << "Condition is never changed";

  ShouldAnalyzeLoopConditions = false;

  mStorage.EndScope();
}

void DeadCodeAnalysis::Visit(const ASTDoWhile *Stmt) {
  mStorage.StartScope();

  bool InfiniteLoopCheckPerformed = false;
  InfiniteLoopCheck(Stmt->Condition(), InfiniteLoopCheckPerformed);

  Stmt->Body()->Accept(this);

  mStorage.EndScope();
}

void DeadCodeAnalysis::InfiniteLoopCheck(const ASTNode *Stmt,
                                         bool &WasChecked) {
  if (mStorage.Lookup("break") || mStorage.Lookup("return"))
    return;

  if (Stmt->Is(AST_BOOLEAN_LITERAL)) {
    auto *Bool = static_cast<const ASTBool *>(Stmt);
    if (Bool->Value())
      weak::CompileWarning(Bool) << "Infinite loop";
    WasChecked = true;
  }

  if (Stmt->Is(AST_INTEGER_LITERAL)) {
    auto *Num = static_cast<const ASTNumber *>(Stmt);
    if (Num->Value() > 0)
      weak::CompileWarning(Num) << "Infinite loop";
    WasChecked = true;
  }
}

} // namespace weak