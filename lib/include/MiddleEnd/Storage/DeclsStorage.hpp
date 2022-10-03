/* DeclsStorage.hpp - Storage for LLVM declarations.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_DECLS_STORAGE_HPP
#define WEAK_COMPILER_MIDDLE_END_DECLS_STORAGE_HPP

#include <string_view>
#include <unordered_map>

namespace llvm {
class AllocaInst;
} // namespace llvm

namespace weak {
namespace middleEnd {

/// \brief Storage for LLVM declarations.
class DeclsStorage {
  /// Entity stored inside. Needed to handle
  /// erasure of IR objects with the end of
  /// scopes.
  struct DeclRecord {
    /// How much variable is nested.
    unsigned Depth;
    /// Pointer.
    llvm::AllocaInst *Value;
  };

public:
  /// Begin new scope; increment scope depth.
  void StartScope();

  /// Terminate scope, destroy all stored variables; decrement scope depth.
  void EndScope();

  /// Add variable at current depth.
  void Push(std::string_view Name, llvm::AllocaInst *Value);

  /// Try to retrieve variable by name.
  ///
  /// \return Stored value if present, null otherwise.
  llvm::AllocaInst *Lookup(std::string_view Name) const;

private:
  unsigned CurrentDepth{0U};

  using Hash = size_t;
  std::unordered_multimap<Hash, DeclRecord> InnerScopes;
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_DECLS_STORAGE_HPP
