/* Sema.cpp - Semantic analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Sema/Sema.h"
#include "FrontEnd/AST/AST.h"
#include "Utility/Diagnostic.h"
#include <unordered_map>

namespace std {
hash()->hash<std::string_view>;
} // namespace std

namespace weak {

struct Sema::Storage {
  struct Record {
    /// How much variable is nested.
    unsigned Depth;
    /// Pointer.
    const ASTNode *Value;
  };

  /// Begin new scope; increment scope depth.
  void StartScope();

  /// Terminate scope, destroy all stored variables; decrement scope depth.
  void EndScope();

  /// Add variable at current depth.
  void Push(std::string_view Name, const ASTNode *Value);

  /// Try to retrieve variable by name.
  const ASTNode *Lookup(std::string_view Name) const;

private:
  unsigned mDepth{0U};

  using Hash = size_t;
  std::unordered_multimap<Hash, Record> mScopes;
} mStorage; ///< Storage for declarations.

void Sema::Storage::Push(std::string_view Name, const ASTNode *Value) {
  mScopes.emplace(std::hash{}(Name), Storage::Record{mDepth, Value});
}

const ASTNode *Sema::Storage::Lookup(std::string_view Name) const {
  auto It = mScopes.find(std::hash{}(Name));

  if (It == mScopes.end())
    return nullptr;

  auto &Decl = It->second;
  if (Decl.Depth > mDepth)
    return nullptr;

  return Decl.Value;
}

void Sema::Storage::StartScope() { ++mDepth; }

void Sema::Storage::EndScope() {
  for (auto It = mScopes.begin(); It != mScopes.end();)
    if (It->second.Depth == mDepth)
      It = mScopes.erase(It);
    else
      ++It;
  --mDepth;
}

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

void Sema::Visit(const ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  Stmt->RHS()->Accept(this);
}

void Sema::Visit(const ASTUnary *Stmt) {
  if (auto *Op = Stmt->Operand();
      !Op->Is(AST_SYMBOL) && !Op->Is(AST_ARRAY_ACCESS))
    weak::CompileError(Stmt)
        << "Variable as argument of unary operator expected";

  Stmt->Operand()->Accept(this);
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
  mStorage->EndScope();
  /// This is to have function outside.
  mStorage->Push(Decl->Name(), Decl);

  if (Decl->ReturnType() == TOK_VOID && mWasReturnStmt) {
    auto [LineNo, ColNo] = mLastReturnLoc;
    weak::CompileError(LineNo, ColNo)
        << "Cannot return value from void function";
  }

  mWasReturnStmt = false;
}

void Sema::Visit(const ASTFunctionCall *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);

  const ASTNode *Func = mStorage->Lookup(Stmt->Name());

  if (!Func->Is(AST_FUNCTION_DECL) && !Func->Is(AST_FUNCTION_PROTOTYPE))
    weak::CompileError(Stmt) << "" << Stmt->Name() << " is not a function";

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
}

void Sema::Visit(const ASTSymbol *Stmt) {
  AssertIsDeclared(Stmt->Name(), Stmt);
}

void Sema::Visit(const ASTCompound *Stmt) {
  mStorage->StartScope();
  for (ASTNode *S : Stmt->Stmts())
    S->Accept(this);
  mStorage->EndScope();
}

void Sema::Visit(const ASTReturn *Stmt) {
  Stmt->Operand()->Accept(this);
  mWasReturnStmt = true;
  mLastReturnLoc = std::pair(Stmt->LineNo(), Stmt->ColumnNo());
}

} // namespace weak