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

/// \brief Unreachable code detector.
///
/// \note Must be called after VariableUseAnalysis, otherwise
///       we can get wierd errors such as SIGSEGV on
///       access to unknown variables.
class DeadCodeAnalysis : public Analysis {
public:
  DeadCodeAnalysis(ASTNode *Root);

  void Analyze() override;

private:
  void Visit(const ASTBreak *) override;
  void Visit(const ASTReturn *) override;

  void Visit(const ASTBinary *) override;
  void Visit(const ASTUnary *) override;

  void Visit(const ASTCompound *) override;

  void Visit(const ASTVarDecl *) override;
  void Visit(const ASTArrayDecl *) override;
  /// \note: Needed to have special scope to isolate
  ///        return statements.
  void Visit(const ASTFunctionDecl *) override;

  void Visit(const ASTSymbol *) override;

  void Visit(const ASTIf *) override;

  void Visit(const ASTFor *) override;
  void Visit(const ASTWhile *) override;
  void Visit(const ASTDoWhile *) override;

  /// Check if given statement always evaluates to true or false.
  /// Used in loops and if statements.
  void AlwaysTrueOrFalseCheck(const ASTNode *Stmt, bool &WasChecked);

  /// Check if loop have explicit exit and cannot stuck forever.
  ///
  /// Possible reasons to warning are:
  ///   1) `true` or numbers > 0 in conditions,
  ///   2) no changes of any variables from condition,
  ///   3) function call in condition, since by language design,
  ///      all functions are "pure" and cannot change state of program.
  void RunLoopAnalysis(ASTNode *Condition, ASTNode *Body,
                       ASTNode *ForIncrement = nullptr);

  void AddUseForVariable(std::string_view Name, bool AddMutableUse);

  /// Analyzed AST.
  ASTNode *mRoot;

  ASTStorage mStorage;

  using UseStorage = std::vector<ASTStorage::Declaration>;
  /// Needed to compute use counts before and after loop conditions
  /// to detect infinite loops.
  std::vector<UseStorage> mCollectedUses;

  bool mShouldAnalyzeLoopConditions{false};
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_DEAD_CODE_ANALYSIS_H