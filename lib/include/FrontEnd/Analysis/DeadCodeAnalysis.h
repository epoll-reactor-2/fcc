/* DeadCodeAnalysis.h - Unreachable code detector.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_DEAD_CODE_ANALYSIS_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_DEAD_CODE_ANALYSIS_H

#include "FrontEnd/Analysis/ASTStorage.h"
#include "FrontEnd/Analysis/Analysis.h"
#include <map>

namespace weak {

class DeadCodeAnalysis : public Analysis {
public:
  DeadCodeAnalysis(ASTNode *Root);

  void Analyze() override;

private:
  // Loop exit points.
  void Visit(const ASTBreak *) override;
  void Visit(const ASTReturn *) override;

  void Visit(const ASTFor *) override;
  void Visit(const ASTWhile *) override;
  void Visit(const ASTDoWhile *) override;

  void DoInfiniteLoopCheck(const ASTNode *);

  /// Analyzed root AST node.
  ASTNode *mRoot;

  ASTStorage mStorage;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_DEAD_CODE_ANALYSIS_H