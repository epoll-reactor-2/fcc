/* ASTStorage.cpp - Storage for declarations being AST nodes.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/ASTStorage.h"
#include <cassert>

namespace std {
hash()->hash<std::string_view>;
} // namespace std

namespace weak {

void ASTStorage::StartScope() { ++mDepth; }

void ASTStorage::EndScope() {
  for (auto It = mScopes.begin(); It != mScopes.end();)
    if (It->second.Depth == mDepth)
      It = mScopes.erase(It);
    else
      ++It;
  --mDepth;
}

void ASTStorage::Push(std::string_view Name, ASTNode *Decl) {
  mScopes.emplace(std::hash{}(Name),
                  Declaration{Decl, Name.data(), /*Uses=*/0, mDepth});
}

ASTStorage::Declaration *ASTStorage::Lookup(std::string_view Name) {
  auto It = mScopes.find(std::hash{}(Name));

  if (It == mScopes.end())
    return nullptr;

  auto &Decl = It->second;
  if (Decl.Depth > mDepth)
    return nullptr;

  return &Decl;
}

void ASTStorage::AddUse(std::string_view Stmt) {
  Declaration &R = FindUse(Stmt);
  ++R.Uses;
}

std::vector<ASTStorage::Declaration *> ASTStorage::CurrScopeUses() {
  std::vector<Declaration *> Uses;

  for (auto &It : mScopes) {
    auto &[Hash, Record] = It;
    if (Record.Depth == mDepth)
      Uses.push_back(&Record);
  }

  return Uses;
}

ASTStorage::Declaration &ASTStorage::FindUse(std::string_view Name) {
  auto It = mScopes.find(std::hash{}(Name));

  assert(It != mScopes.end() && "Variable expected to be declared before");
  auto &Decl = It->second;
  assert(Decl.Depth <= mDepth && "Variable expected to be declared before");

  return Decl;
}

unsigned ASTStorage::CurrentDepth() { return mDepth; }

} // namespace weak