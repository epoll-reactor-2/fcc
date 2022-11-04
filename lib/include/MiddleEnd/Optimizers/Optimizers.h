/* Optimizations.h - Optimization passes for LLVM IR.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_OPTIMIZERS_H
#define WEAK_COMPILER_MIDDLE_END_OPTIMIZERS_H

#include "llvm/IR/Module.h"

/// Global due to clEnumVal use.
enum WeakOptimizationLevel { O0 = 0, O1, O2, O3 };

namespace weak {

/// Perform built-in LLVM optimizations of given level.
///
/// \todo Implement own optimizations.
void RunBuiltinLLVMOptimizationPass(llvm::Module &M,
                                    WeakOptimizationLevel OptLvl);

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_OPTIMIZERS_H