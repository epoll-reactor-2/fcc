/* ASTStorage.h - Storage for declarations being AST nodes.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H

#include "FrontEnd/AST/ASTNode.h"
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace weak {

struct ASTStorage {
  struct Declaration {
    /// Pointer.
    const ASTNode *Value{nullptr};
    /// Variable name.
    std::string Name;
    /// How many times variable was used (accessed).
    unsigned Uses{0U};
    /// How many times variable was changed.
    unsigned MutableUses{0U};
    /// How much variable is nested.
    unsigned Depth{0U};
  };

  /// Begin new scope; increment scope depth.
  void StartScope();

  /// Terminate scope, destroy all stored variables; decrement scope depth.
  void EndScope();

  /// Add variable at current depth.
  void Push(std::string_view Name, const ASTNode *Decl);

  /// Try to retrieve variable by name.
  Declaration *Lookup(std::string_view Name);

  /// \brief Add use for variable.
  ///
  /// If use count is equal to 0, it mean that variable
  /// was not used anywhere and we can emit warning about it.
  void AddUse(std::string_view Stmt);

  /// \brief Get set of all declared variables in current scope.
  ///
  /// Needed to determine unused variables.
  std::vector<Declaration *> CurrScopeUses();

  /// Return current depth.
  unsigned CurrentDepth();

private:
  Declaration &FindUse(std::string_view Name);

  unsigned mDepth{0U};

  using Hash = size_t;
  std::unordered_multimap<Hash, Declaration> mScopes;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H