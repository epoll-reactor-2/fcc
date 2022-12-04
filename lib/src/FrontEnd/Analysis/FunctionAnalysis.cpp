/* FunctionAnalysis.cpp - Semantic analyzer to determine issues with functions.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/FunctionAnalysis.h"
#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTFunctionCall.h"
#include "FrontEnd/AST/ASTFunctionDecl.h"
#include "FrontEnd/AST/ASTFunctionPrototype.h"
#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/AST/ASTReturn.h"
#include "Utility/Diagnostic.h"
#include "Utility/Unreachable.h"

namespace weak {

FunctionAnalysis::FunctionAnalysis(ASTNode *Root)
  : mRoot(Root)
  , mWasReturnStmt(false)
  , mLastReturnLoc(0, 0) {}

void FunctionAnalysis::Analyze() {
  mRoot->Accept(this);
}

void FunctionAnalysis::Visit(ASTReturn *Stmt) {
  if (auto *O = Stmt->Operand()) {
    O->Accept(this);
    mWasReturnStmt = true;
    mLastReturnLoc = {Stmt->LineNo(), Stmt->ColumnNo()};
  }
}

static size_t FunctionASTArgsCount(ASTNode *Stmt) {
  if (Stmt->Is(AST_FUNCTION_DECL))
    return static_cast<ASTFunctionDecl *>(Stmt)->Args().size();

  if (Stmt->Is(AST_FUNCTION_PROTOTYPE))
    return static_cast<ASTFunctionPrototype *>(Stmt)->Args().size();

  Unreachable("Expected function declaration or prototype.");
}

void FunctionAnalysis::Visit(ASTFunctionCall *Stmt) {
  ASTNode *Func = mStorage.Lookup(Stmt->Name())->AST;

  unsigned CallArgsSize = Stmt->Args().size();
  unsigned DeclArgsSize = FunctionASTArgsCount(Func);

  if (DeclArgsSize != CallArgsSize)
    weak::CompileError(Stmt)
      << "Arguments size mismatch: "
      << CallArgsSize
      << " got, but "
      << DeclArgsSize
      << " expected";

  for (ASTNode *A : Stmt->Args())
    A->Accept(this);
}

void FunctionAnalysis::Visit(ASTFunctionDecl *Decl) {
  mStorage.Push(Decl->Name(), Decl);

  /// Don't need to analyze arguments though.
  Decl->Body()->Accept(this);

  auto Reset = [this] {
    mWasReturnStmt = false;
    mLastReturnLoc = {0, 0};
  };

  if (mWasReturnStmt && Decl->ReturnType() == DT_VOID) {
    auto [LineNo, ColNo] = mLastReturnLoc;
    Reset();
    weak::CompileError(LineNo, ColNo)
      << "Cannot return value from void function";
  }

  if (!mWasReturnStmt && Decl->ReturnType() != DT_VOID) {
    Reset();
    weak::CompileError(Decl) << "Expected return value";
  }
}

void FunctionAnalysis::Visit(ASTFunctionPrototype *Stmt) {
  mStorage.Push(Stmt->Name(), Stmt);
}

} // namespace weak