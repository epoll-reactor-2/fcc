/* FunctionAnalysis.h - Semantic analyzer to determine issues with functions.
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
  void Visit(ASTReturn *) override;

  void Visit(ASTFunctionDecl *) override;
  void Visit(ASTFunctionCall *) override;
  void Visit(ASTFunctionPrototype *) override;

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