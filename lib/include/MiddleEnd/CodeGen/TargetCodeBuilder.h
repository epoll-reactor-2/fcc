/* TargetCodeBuilder.h - Builder of executable code from LLVM IR.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TARGET_CODE_BUILDER_H
#define WEAK_COMPILER_MIDDLE_END_TARGET_CODE_BUILDER_H

#include "llvm/IR/Module.h"

namespace weak {

/// Builder of executable code from LLVM IR.
class TargetCodeBuilder {
public:
  TargetCodeBuilder(llvm::Module &Module,
                    std::string_view ObjFilePath);

  /// Compile LLVM IR to object code and write it to output file.
  ///
  /// \note In debugging purposes this function uses clang to somehow emit
  ///       executable file.
  /// \todo Judge how properly do emitting of binaries without bash stubs.
  void Build();

private:
  /// Reference to global LLVM stuff.
  llvm::Module &mIRModule;
  /// Reference to global LLVM stuff.
  std::string mObjFilePath;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_TARGET_CODE_BUILDER_H