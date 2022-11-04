/* VariableUseAnalysis.h - Semantic analyzer to determine variable issues.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USE_ANALYSIS_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USE_ANALYSIS_H

#include "FrontEnd/Analysis/ASTStorage.h"
#include "FrontEnd/Analysis/Analyzer.h"
#include <string>

namespace weak {

/// \brief Semantic analyzer to determine variable issues.
///
/// Performs checks if variable was properly declared and emits
/// warnings about unused variables.
class VariableUseAnalysis : public Analyzer {
public:
  VariableUseAnalysis(ASTNode *Root);

  void Analyze() override;

private:
  // Operators.
  void Visit(const ASTBinary *) override;
  void Visit(const ASTUnary *) override;

  // Loop statements.
  void Visit(const ASTFor *) override;

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

  /// Check if given AST node is symbol/array access operator and
  /// increment use counter for this.
  void AddUseOnVarAccess(ASTNode *);

  void AssertIsDeclared(std::string_view Name, const ASTNode *InformAST);
  void AssertIsNotDeclared(std::string_view Name, const ASTNode *InformAST);

  void MakeUnusedVarAndFuncAnalysis();
  void MakeUnusedVarAnalysis();

  /// Storage for declarations.
  ASTStorage mStorage;

  /// Analyzed root AST node.
  ASTNode *mRoot;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USE_ANALYSIS_H