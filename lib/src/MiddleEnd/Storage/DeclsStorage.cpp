/* DeclsStorage.hpp - Storage for LLVM declarations.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/Storage/DeclsStorage.hpp"

namespace std {
hash()->hash<std::string_view>;
} // namespace std

namespace weak {
namespace middleEnd {

DeclsStorage::DeclsStorage() : CurrentDepth(0U), InnerScopes() {}

void DeclsStorage::Push(std::string_view Name, llvm::AllocaInst *Value) {
  InnerScopes.emplace(std::hash{}(Name), DeclRecord{CurrentDepth, Value});
}

llvm::AllocaInst *DeclsStorage::Lookup(std::string_view Name) {
  auto It = InnerScopes.find(std::hash{}(Name));

  if (It == InnerScopes.end())
    return nullptr;

  auto &Decl = It->second;
  if (Decl.Depth > CurrentDepth)
    return nullptr;

  return Decl.Value;
}

void DeclsStorage::StartScope() { ++CurrentDepth; }

void DeclsStorage::EndScope() {
  for (auto It = InnerScopes.begin(); It != InnerScopes.end();)
    if (It->second.Depth == CurrentDepth)
      It = InnerScopes.erase(It);
    else
      ++It;
  --CurrentDepth;
}

} // namespace middleEnd
} // namespace weak