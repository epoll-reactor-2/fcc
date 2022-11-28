/* Storage.cpp - Storage for LLVM declarations.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/Storage/Storage.h"

namespace std {
hash() -> hash<std::string_view>;
} // namespace std

namespace weak {

void Storage::Push(std::string_view Name, llvm::AllocaInst *Value) {
  mScopes.emplace(std::hash{}(Name), DeclRecord{mDepth, Value});
}

llvm::AllocaInst *Storage::Lookup(std::string_view Name) const {
  auto It = mScopes.find(std::hash{}(Name));

  if (It == mScopes.end())
    return nullptr;

  auto &Decl = It->second;
  if (Decl.Depth > mDepth)
    return nullptr;

  return Decl.Value;
}

void Storage::StartScope() {
  ++mDepth;
}

void Storage::EndScope() {
  for (auto It = mScopes.begin(); It != mScopes.end();)
    if (It->second.Depth == mDepth)
      It = mScopes.erase(It);
    else
      ++It;
  --mDepth;
}

} // namespace weak