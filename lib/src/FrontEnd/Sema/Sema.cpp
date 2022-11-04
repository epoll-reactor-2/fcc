/* Sema.cpp - Semantic analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Sema/Sema.h"
#include "FrontEnd/AST/AST.h"
#include "Utility/Diagnostic.h"
#include <algorithm>
#include <cassert>
#include <unordered_map>

namespace std {
hash()->hash<std::string_view>;
} // namespace std

namespace weak {

struct Sema::Storage {
  struct Record {
    /// Pointer.
    const ASTNode *Value{nullptr};
    /// Variable name.
    std::string Name;
    /// How many times variable was used (accessed).
    unsigned Usages{0U};
    /// How much variable is nested.
    unsigned Depth{0U};
  };

  /// Begin new scope; increment scope depth.
  void StartScope() { ++mDepth; }

  /// Terminate scope, destroy all stored variables; decrement scope depth.
  void EndScope() {
    for (auto It = mScopes.begin(); It != mScopes.end();)
      if (It->second.Depth == mDepth)
        It = mScopes.erase(It);
      else
        ++It;
    --mDepth;
  }

  /// Add variable at current depth.
  void Push(std::string_view Name, const ASTNode *Decl) {
    mScopes.emplace(std::hash{}(Name),
                    Storage::Record{Decl, Name.data(), /*Usages=*/0, mDepth});
  }

  /// Try to retrieve variable by name.
  const ASTNode *Lookup(std::string_view Name) const {
    auto It = mScopes.find(std::hash{}(Name));

    if (It == mScopes.end())
      return nullptr;

    auto &Decl = It->second;
    if (Decl.Depth > mDepth)
      return nullptr;

    return Decl.Value;
  }

  /// \brief Add usage for variable.
  ///
  /// If usage count is equal to 0, it mean that variable
  /// was not used anywhere and we can emit warning about it.
  void AddUsage(std::string_view Stmt) {
    Record &R = FindUsage(Stmt);
    ++R.Usages;
  }

  /// \brief Get set of all declared variables in current scope.
  ///
  /// Needed to determine unused variables.
  std::vector<Record *> UsagesForCurrentScope() {
    std::vector<Record *> Usages;

    for (auto &It : mScopes) {
      auto &[Hash, Record] = It;
      if (Record.Depth != mDepth)
        continue;
      Usages.push_back(&Record);
    }

    return Usages;
  }

private:
  Record &FindUsage(std::string_view Name) {
    auto It = mScopes.find(std::hash{}(Name));

    if (It == mScopes.end())
      assert(false && "Variable expected to be declared before");

    auto &Decl = It->second;
    if (Decl.Depth > mDepth)
      assert(false && "Variable expected to be declared before");

    return Decl;
  }

  unsigned mDepth{0U};

  using Hash = size_t;
  std::unordered_multimap<Hash, Record> mScopes;
}; ///< Storage for declarations.

} // namespace weak

namespace weak {

Sema::Sema(ASTNode *Root)
    : mStorage(new Storage), mRoot(Root), mWasReturnStmt(false),
      mLastReturnLoc(0, 0) {}

Sema::~Sema() { delete mStorage; }

void Sema::AssertIsDeclared(std::string_view Name, const ASTNode *InformAST) {
  if (!mStorage->Lookup(Name))
    weak::CompileError(InformAST)
        << (InformAST->Is(AST_FUNCTION_CALL) ? "Function" : "Variable") << " `"
        << Name << "` not found";
}

void Sema::AssertIsNotDeclared(std::string_view Name,
                               const ASTNode *InformAST) {
  if (mStorage->Lookup(Name))
    weak::CompileError(InformAST)
        << (InformAST->Is(AST_FUNCTION_CALL) ? "Function" : "Variable") << " `"
        << Name << "` already declared";
}

void Sema::Analyze() { mRoot->Accept(this); }

void Sema::AddUsageOnVarAccess(ASTNode *Stmt) {
  if (Stmt->Is(AST_SYMBOL)) {
    auto *S = static_cast<ASTSymbol *>(Stmt);
    mStorage->AddUsage(S->Name());
  }

  if (Stmt->Is(AST_ARRAY_ACCESS)) {
    auto *A = static_cast<ASTArrayAccess *>(Stmt);
    mStorage->AddUsage(A->Name());
  }
}

void Sema::Visit(const ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);

  AddUsageOnVarAccess(Stmt->LHS());
  AddUsageOnVarAccess(Stmt->RHS());
}

void Sema::Visit(const ASTUnary *Stmt) {
  if (auto *Op = Stmt->Operand();
      !Op->Is(AST_SYMBOL) && !Op->Is(AST_ARRAY_ACCESS))
    weak::CompileError(Stmt)
        << "Variable as argument of unary operator expected";

  Stmt->Operand()->Accept(this);

  AddUsageOnVarAccess(Stmt->Operand());
}

void Sema::Visit(const ASTFor *Stmt) {
  mStorage->StartScope();

  if (auto *I = Stmt->Init())
    I->Accept(this);

  if (auto *C = Stmt->Condition())
    C->Accept(this);

  if (auto *I = Stmt->Increment())
    I->Accept(this);

  Stmt->Body()->Accept(this);
  mStorage->EndScope();
}

void Sema::Visit(const ASTWhile *Stmt) {
  Stmt->Condition()->Accept(this);
  Stmt->Body()->Accept(this);
}

void Sema::Visit(const ASTDoWhile *Stmt) {
  Stmt->Body()->Accept(this);
  Stmt->Condition()->Accept(this);
}

void Sema::Visit(const ASTIf *Stmt) {
  Stmt->Condition()->Accept(this);
  Stmt->ThenBody()->Accept(this);

  if (auto *E = Stmt->ElseBody())
    E->Accept(this);
}

void Sema::Visit(const ASTFunctionDecl *Decl) {
  mStorage->StartScope();
  /// This is to have function in recursive calls.
  mStorage->Push(Decl->Name(), Decl);
  for (ASTNode *A : Decl->Args())
    A->Accept(this);

  Decl->Body()->Accept(this);

  MakeUnusedVarAnalysis();

  mStorage->EndScope();
  /// This is to have function outside.
  mStorage->Push(Decl->Name(), Decl);

  if (mWasReturnStmt && Decl->ReturnType() == TOK_VOID) {
    auto [LineNo, ColNo] = mLastReturnLoc;
    weak::CompileError(LineNo, ColNo)
        << "Cannot return value from void function";
  }

  mWasReturnStmt = false;
}

void Sema::Visit(const ASTFunctionCall *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);

  const ASTNode *Func = mStorage->Lookup(Stmt->Name());

  /// Used to handle expressions like that
  /// int value = 0;
  /// value();
  if (!Func->Is(AST_FUNCTION_DECL) && !Func->Is(AST_FUNCTION_PROTOTYPE))
    weak::CompileError(Stmt) << "`" << Stmt->Name() << "` is not a function";

  mStorage->AddUsage(Stmt->Name());

  const auto *Decl = static_cast<const ASTFunctionDecl *>(Func);

  {
    auto CallArgsSize = Stmt->Args().size();
    auto DeclArgsSize = Decl->Args().size();

    if (DeclArgsSize != CallArgsSize)
      weak::CompileError(Stmt) << "Arguments size mismatch: " << CallArgsSize
                               << " got, but " << DeclArgsSize << " expected";
  }

  for (ASTNode *A : Stmt->Args())
    A->Accept(this);
}

void Sema::Visit(const ASTFunctionPrototype *Stmt) {
  AssertIsNotDeclared(Stmt->Name(), Stmt);

  for (ASTNode *A : Stmt->Args())
    A->Accept(this);

  mStorage->Push(Stmt->Name(), Stmt);
}

void Sema::Visit(const ASTArrayDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);
  mStorage->Push(Decl->Name(), Decl);
}

void Sema::Visit(const ASTVarDecl *Decl) {
  AssertIsNotDeclared(Decl->Name(), Decl);
  mStorage->Push(Decl->Name(), Decl);
}

void Sema::Visit(const ASTArrayAccess *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
  mStorage->AddUsage(Stmt->Name());
}

void Sema::Visit(const ASTSymbol *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
  mStorage->AddUsage(Stmt->Name());
}

void Sema::Visit(const ASTCompound *Stmt) {
  mStorage->StartScope();
  for (ASTNode *S : Stmt->Stmts())
    S->Accept(this);

  MakeUnusedVarAndFuncAnalysis();

  mStorage->EndScope();
}

void Sema::Visit(const ASTReturn *Stmt) {
  Stmt->Operand()->Accept(this);
  mWasReturnStmt = true;
  mLastReturnLoc = std::pair(Stmt->LineNo(), Stmt->ColumnNo());
}

void Sema::MakeUnusedVarAndFuncAnalysis() {
  for (auto *U : mStorage->UsagesForCurrentScope()) {
    bool IsFunction = U->Value->Is(AST_FUNCTION_DECL);
    bool IsMainFunction = false;

    if (IsFunction)
      IsMainFunction =
          static_cast<const ASTFunctionDecl *>(U->Value)->Name() == "main";

    if (U->Usages == 0 && !IsMainFunction)
      weak::CompileWarning(U->Value) << (IsFunction ? "Function" : "Variable")
                                     << " `" << U->Name << "` is never used";
  }
}

void Sema::MakeUnusedVarAnalysis() {
  for (auto *U : mStorage->UsagesForCurrentScope()) {
    bool IsFunction = U->Value->Is(AST_FUNCTION_DECL);

    if (U->Usages == 0 && !IsFunction)
      weak::CompileWarning(U->Value) << "Variable"
                                     << " `" << U->Name << "` is never used";
  }
}

} // namespace weak
