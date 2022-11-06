/* Analysis.h - Virtual class to have Analyze() method.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_ANALYSIS_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_ANALYSIS_H

#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

/// Class for case if we have several semantic analyzers, added,
/// for example with compiler flags such as -Wunused, -Wall, etc.,
/// to be able to do
///   vector<Analyzer *> Analyzers;
///   /* Collect needed ones. */
///   for (auto *A : Analyzers)
///     A->Analyze();
struct Analysis : public ASTVisitor {
  virtual ~Analysis() = default;

  virtual void Analyze() = 0;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_ANALYSIS_H