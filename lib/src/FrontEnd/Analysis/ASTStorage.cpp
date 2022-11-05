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

/// Terminate scope, destroy all stored variables; decrement scope depth.
void ASTStorage::EndScope() {
  for (auto It = mScopes.begin(); It != mScopes.end();)
    if (It->second.Depth == mDepth)
      It = mScopes.erase(It);
    else
      ++It;
  --mDepth;
}

/// Add variable at current depth.
void ASTStorage::Push(std::string_view Name, const ASTNode *Decl) {
  mScopes.emplace(std::hash{}(Name), Declaration{Decl, Name.data(), /*Uses=*/0,
                                                 /*MutableUses=*/0, mDepth});
}

/// Try to retrieve variable by name.
ASTStorage::Declaration *ASTStorage::Lookup(std::string_view Name) {
  auto It = mScopes.find(std::hash{}(Name));

  if (It == mScopes.end())
    return nullptr;

  auto &Decl = It->second;
  if (Decl.Depth > mDepth)
    return nullptr;

  return &Decl;
}

/// \brief Add use for variable.
///
/// If use count is equal to 0, it mean that variable
/// was not used anywhere and we can emit warning about it.
void ASTStorage::AddUse(std::string_view Stmt) {
  Declaration &R = FindUse(Stmt);
  ++R.Uses;
}

/// \brief Get set of all declared variables in current scope.
///
/// Needed to determine unused variables.
std::vector<ASTStorage::Declaration *> ASTStorage::CurrScopeUses() {
  std::vector<Declaration *> Uses;

  for (auto &It : mScopes) {
    auto &[Hash, Record] = It;
    if (Record.Depth != mDepth)
      continue;
    Uses.push_back(&Record);
  }

  return Uses;
}

ASTStorage::Declaration &ASTStorage::FindUse(std::string_view Name) {
  auto It = mScopes.find(std::hash{}(Name));

  if (It == mScopes.end())
    assert(false && "Variable expected to be declared before");

  auto &Decl = It->second;
  if (Decl.Depth > mDepth)
    assert(false && "Variable expected to be declared before");

  return Decl;
}

unsigned int ASTStorage::CurrentDepth() { return mDepth; }

} // namespace weak