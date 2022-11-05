/* DeadCodeAnalysis.h - Unreachable code detector.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_DEAD_CODE_ANALYSIS_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_DEAD_CODE_ANALYSIS_H

#include "FrontEnd/Analysis/ASTStorage.h"
#include "FrontEnd/Analysis/Analysis.h"
#include <vector>

namespace weak {

class DeadCodeAnalysis : public Analysis {
public:
  DeadCodeAnalysis(ASTNode *Root);

  void Analyze() override;

private:
  // Loop exit points.
  void Visit(const ASTBreak *) override;
  void Visit(const ASTReturn *) override;

  void Visit(const ASTVarDecl *) override;
  void Visit(const ASTArrayDecl *) override;

  void Visit(const ASTSymbol *) override;

  void Visit(const ASTFor *) override;
  void Visit(const ASTWhile *) override;
  void Visit(const ASTDoWhile *) override;

  void InfiniteLoopCheck(const ASTNode *Stmt, bool &WasChecked);

  void RunLoopAnalysis(ASTNode *Condition, ASTNode *Body,
                       ASTNode *ForIncrement = nullptr);

  /// Analyzed root AST node.
  ASTNode *mRoot;

  ASTStorage mStorage;

  /// Used to compute use counts before and after loop conditions
  /// to detect infinite loops.
  std::vector<ASTStorage::Declaration> mCollectedUses;

  bool ShouldAnalyzeLoopConditions{false};
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_DEAD_CODE_ANALYSIS_H