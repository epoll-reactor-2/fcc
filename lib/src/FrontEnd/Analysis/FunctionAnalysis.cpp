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

namespace weak {

FunctionAnalysis::FunctionAnalysis(ASTNode *Root)
    : mRoot(Root), mWasReturnStmt(false), mLastReturnLoc(0, 0) {}

void FunctionAnalysis::Analyze() { mRoot->Accept(this); }

void FunctionAnalysis::Visit(const ASTReturn *Stmt) {
  if (auto *O = Stmt->Operand()) {
    O->Accept(this);
    mWasReturnStmt = true;
    mLastReturnLoc = {Stmt->LineNo(), Stmt->ColumnNo()};
  }
}

static unsigned FunctionASTArgsCount(const ASTNode *Stmt) {
  if (Stmt->Is(AST_FUNCTION_DECL))
    return static_cast<const ASTFunctionDecl *>(Stmt)->Args().size();

  if (Stmt->Is(AST_FUNCTION_PROTOTYPE))
    return static_cast<const ASTFunctionPrototype *>(Stmt)->Args().size();

  Unreachable();
}

void FunctionAnalysis::Visit(const ASTFunctionCall *Stmt) {
  const ASTNode *Func = mStorage.Lookup(Stmt->Name())->Value;

  unsigned CallArgsSize = Stmt->Args().size();
  unsigned DeclArgsSize = FunctionASTArgsCount(Func);

  if (DeclArgsSize != CallArgsSize)
    weak::CompileError(Stmt) << "Arguments size mismatch: " << CallArgsSize
                             << " got, but " << DeclArgsSize << " expected";

  for (ASTNode *A : Stmt->Args())
    A->Accept(this);
}

void FunctionAnalysis::Visit(const ASTFunctionDecl *Decl) {
  mStorage.Push(Decl->Name(), Decl);

  /// Don't need to analyze arguments though.
  Decl->Body()->Accept(this);

  if (mWasReturnStmt && Decl->ReturnType() == TOK_VOID) {
    auto [LineNo, ColNo] = mLastReturnLoc;
    weak::CompileError(LineNo, ColNo)
        << "Cannot return value from void function";
  }

  mWasReturnStmt = false;
  mLastReturnLoc = {0, 0};
}

void FunctionAnalysis::Visit(const ASTFunctionPrototype *Stmt) {
  mStorage.Push(Stmt->Name(), Stmt);
}

} // namespace weak