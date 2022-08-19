#ifndef WEAK_COMPILER_MIDDLE_END_DECLS_STORAGE_HPP
#define WEAK_COMPILER_MIDDLE_END_DECLS_STORAGE_HPP

#include <string_view>
#include <unordered_map>

namespace llvm {
class AllocaInst;
} // namespace llvm

namespace weak {
namespace middleEnd {

/// Storage for LLVM declarations.
class DeclsStorage {
  // Entity stored inside. Needed to handle
  // erasure of IR objects with the end of
  // scopes.
  struct DeclRecord {
    unsigned Depth;
    llvm::AllocaInst *Value;
  };

public:
  DeclsStorage();

  /// Begin new scope.
  void StartScope();
  /// Terminate scope, destroy all stored variables.
  void EndScope();

  /// Add variable at current depth.
  void Push(std::string_view Name, llvm::AllocaInst *Value);

  /// Try to retrieve variable by name.
  /// \return Stored value if present, null otherwise.
  llvm::AllocaInst *Lookup(std::string_view Name);

private:
  unsigned CurrentDepth;

  using Hash = size_t;

  std::unordered_multimap<Hash, DeclRecord> InnerScopes;
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_DECLS_STORAGE_HPP
