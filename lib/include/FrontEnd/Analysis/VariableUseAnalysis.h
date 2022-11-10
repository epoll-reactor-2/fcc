/* VariableUseAnalysis.h - Semantic analyzer to determine variable issues.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USE_ANALYSIS_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USE_ANALYSIS_H

#include "FrontEnd/Analysis/ASTStorage.h"
#include "FrontEnd/Analysis/Analysis.h"
#include <string>

namespace weak {

/// \brief Semantic analyzer to determine variable issues.
///
/// Performs checks if variable was properly declared and emits
/// warnings about unused variables.
class VariableUseAnalysis : public Analysis {
public:
  VariableUseAnalysis(ASTNode *Root);

  void Analyze() override;

private:
  // Operators.
  void Visit(ASTBinary *) override;
  void Visit(ASTUnary *) override;

  // Loop statements.
  void Visit(ASTFor *) override;

  // Function statements.
  void Visit(ASTFunctionDecl *) override;
  void Visit(ASTFunctionCall *) override;
  void Visit(ASTFunctionPrototype *) override;

  // Declarations.
  void Visit(ASTArrayDecl *) override;
  void Visit(ASTVarDecl *) override;

  // The rest.
  void Visit(ASTArrayAccess *) override;
  void Visit(ASTSymbol *) override;
  void Visit(ASTCompound *) override;
  void Visit(ASTReturn *) override;

  /// Check if given AST node is symbol/array access operator and
  /// increment use counter for this.
  void AddUseOnVarAccess(ASTNode *);

  void AssertIsDeclared(std::string_view Name, ASTNode *AST);
  void AssertIsNotDeclared(std::string_view Name, ASTNode *AST);

  void MakeUnusedVarAndFuncAnalysis();
  void MakeUnusedVarAnalysis();

  /// Storage for declarations.
  ASTStorage mStorage;

  /// Analyzed root AST node.
  ASTNode *mRoot;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_VARIABLE_USE_ANALYSIS_H