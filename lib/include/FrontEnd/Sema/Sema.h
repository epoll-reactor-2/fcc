/* Sema.h - Semantic analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_SEMA_SEMA_H
#define WEAK_COMPILER_FRONTEND_SEMA_SEMA_H

#include "FrontEnd/AST/ASTVisitor.h"
#include <string>

namespace weak {

/// \brief Semantic analyzer.
///
/// Performs basic syntax checks such as undeclared variable.
class Sema : private ASTVisitor {
  struct Storage;

  /// Storage for declarations.
  Storage *mStorage;

  void AssertIsDeclared(std::string_view Name, const ASTNode *InformAST);
  void AssertIsNotDeclared(std::string_view Name, const ASTNode *InformAST);

  /// Analyzed root AST node.
  ASTNode *mRoot;

  /// To check returns from void function and missing
  /// return in non-void functions.
  bool mWasReturnStmt;

  /// Location of return statement, used to emit errors.
  std::pair<unsigned, unsigned> mLastReturnLoc;

public:
  Sema(ASTNode *Root);

  ~Sema();

  void Analyze();

private:
  // Operators.
  void Visit(const ASTBinary *) override;
  void Visit(const ASTUnary *) override;

  // Loop statements.
  void Visit(const ASTFor *) override;
  void Visit(const ASTWhile *) override;
  void Visit(const ASTDoWhile *) override;

  // Condition statements.
  void Visit(const ASTIf *) override;

  // Function statements.
  void Visit(const ASTFunctionDecl *) override;
  void Visit(const ASTFunctionCall *) override;
  void Visit(const ASTFunctionPrototype *) override;

  // Declarations.
  void Visit(const ASTArrayDecl *) override;
  void Visit(const ASTVarDecl *) override;

  // The rest.
  void Visit(const ASTArrayAccess *) override;
  void Visit(const ASTSymbol *) override;
  void Visit(const ASTCompound *) override;
  void Visit(const ASTReturn *) override;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_SEMA_SEMA_H