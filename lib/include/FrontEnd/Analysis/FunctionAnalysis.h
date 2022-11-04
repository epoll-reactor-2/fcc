/* FunctionAnalysis.h - Semantic analyzer to determine issues with function.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_FUNCTION_ANALYSIS_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_FUNCTION_ANALYSIS_H

#include "FrontEnd/Analysis/ASTStorage.h"
#include "FrontEnd/Analysis/Analysis.h"
#include <utility>

namespace weak {

/// \brief Semantic analyzer to determine function issues.
///
/// \note Should be called after VariableUseAnalysis.
///
/// Performs checks if function call has correct arguments passed,
/// of correct size, etc.
class FunctionAnalysis : public Analysis {
public:
  FunctionAnalysis(ASTNode *Root);

  void Analyze() override;

private:
  void Visit(const ASTReturn *) override;

  void Visit(const ASTFunctionDecl *) override;
  void Visit(const ASTFunctionCall *) override;
  void Visit(const ASTFunctionPrototype *) override;

  /// Analyzed root AST node.
  ASTNode *mRoot;

  ASTStorage mStorage;

  /// To check returns from void function and missing
  /// return in non-void functions.
  bool mWasReturnStmt;

  /// Location of return statement, used to emit errors.
  std::pair<unsigned, unsigned> mLastReturnLoc;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_FUNCTION_ANALYSIS_H