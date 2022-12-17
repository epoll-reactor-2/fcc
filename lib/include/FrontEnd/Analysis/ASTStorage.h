/* ASTStorage.h - Storage for declarations being AST nodes.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/DataType.h"
#include <map>
#include <string>
#include <vector>

namespace weak {

struct ASTStorage {
  struct Declaration {
    ASTNode *AST{nullptr};
    DataType Type{DT_UNKNOWN};
    std::string Name;
    /// How many times variable was accessed.
    unsigned ReadUses{0U};
    /// How many times value was written to variable.
    unsigned WriteUses{0U};
    /// How much variable is nested.
    unsigned Depth{0U};
  };

  /// Begin new scope; increment scope depth.
  void StartScope();

  /// Terminate scope, destroy all stored variables; decrement scope depth.
  void EndScope();

  /// Add variable at current depth.
  void Push(std::string_view Name, ASTNode *Decl);
  /// \copydoc ASTStorage::Push(std::string_view, ASTNode *)
  void Push(std::string_view Name, DataType T, ASTNode *Decl);

  /// Try to retrieve variable by name.
  Declaration *Lookup(std::string_view Name);

  /// \brief Add use for variable.
  void AddReadUse(std::string_view Stmt);

  /// \brief Add use for variable.
  ///
  /// If write use count is equal to 0, it mean that variable
  /// was not used anywhere and we can emit warning about it.
  void AddWriteUse(std::string_view Stmt);

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
  std::multimap<Hash, Declaration> mScopes;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_AST_STORAGE_H