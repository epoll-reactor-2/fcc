/* BuiltinLLVMOptimizationPass.cpp - LLVM IR basic optimization.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/Optimizers/Optimizers.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

void weak::RunBuiltinLLVMOptimizationPass(llvm::Module &IRModule, WeakOptimizationLevel OptLvl) {
  llvm::legacy::FunctionPassManager FPM(&IRModule);
  llvm::PassManagerBuilder PassBuilder;
  PassBuilder.OptLevel = static_cast<unsigned>(OptLvl);
  PassBuilder.populateFunctionPassManager(FPM);

  for (auto &Func : IRModule.getFunctionList())
    FPM.run(Func);
}