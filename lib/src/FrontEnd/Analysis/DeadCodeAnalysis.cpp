/* DeadCodeAnalysis.cpp - Unreachable code detector.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/DeadCodeAnalysis.h"
#include "FrontEnd/AST/ASTBool.h"
#include "FrontEnd/AST/ASTBreak.h"
#include "FrontEnd/AST/ASTDoWhile.h"
#include "FrontEnd/AST/ASTFor.h"
#include "FrontEnd/AST/ASTReturn.h"
#include "FrontEnd/AST/ASTWhile.h"
#include "Utility/Diagnostic.h"
#include <cassert>

namespace weak {

DeadCodeAnalysis::DeadCodeAnalysis(ASTNode *Root) : mRoot(Root) {}

void DeadCodeAnalysis::Analyze() { mRoot->Accept(this); }

void DeadCodeAnalysis::Visit(const ASTBreak *Stmt) {
  mStorage.Push("break", Stmt);
}

void DeadCodeAnalysis::Visit(const ASTReturn *Stmt) {
  mStorage.Push("return", Stmt);
}

void DeadCodeAnalysis::Visit(const ASTFor *) {}

void DeadCodeAnalysis::Visit(const ASTWhile *Stmt) {
  mStorage.StartScope();

  Stmt->Body()->Accept(this);
  DoInfiniteLoopCheck(Stmt->Condition());

  mStorage.EndScope();
}

void DeadCodeAnalysis::Visit(const ASTDoWhile *Stmt) {
  mStorage.StartScope();

  Stmt->Body()->Accept(this);
  DoInfiniteLoopCheck(Stmt->Condition());

  mStorage.EndScope();
}

void DeadCodeAnalysis::DoInfiniteLoopCheck(const ASTNode *Stmt) {
  if (mStorage.Lookup("break") || mStorage.Lookup("return"))
    return;

  if (Stmt->Is(AST_BOOLEAN_LITERAL)) {
    auto *Bool = static_cast<const ASTBool *>(Stmt);
    if (Bool->Value())
      weak::CompileWarning(Bool) << "Infinite loop";
  }

  /// \todo: If condition is a symbol, get it's value from storage cache,
  ///        next check for simple cases, e.g., if it always
  ///        convertible to true and only has one usage.
}

} // namespace weak