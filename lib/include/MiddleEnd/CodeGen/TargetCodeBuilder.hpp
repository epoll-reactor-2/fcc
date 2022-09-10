/* TargetCodeBuilder.hpp - Builder of executable code from LLVM IR.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TARGET_CODE_BUILDER_HPP
#define WEAK_COMPILER_MIDDLE_END_TARGET_CODE_BUILDER_HPP

#include "llvm/IR/Module.h"

namespace weak {

namespace middleEnd {

/// Builder of executable code from LLVM IR.
class TargetCodeBuilder {
public:
  TargetCodeBuilder(llvm::Module &TheModule,
                    std::string_view TheObjectFilePath);

  /// Compile LLVM IR to object code and write it to output file.
  ///
  /// \note In debugging purposes this function uses clang to somehow emit
  ///       executable file.
  /// \todo Decide how properly do emitting of binaries without bash stubs.
  void Build();

private:
  /// Reference to global LLVM stuff.
  llvm::Module &Module;
  /// Reference to global LLVM stuff.
  std::string ObjectFilePath;
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_TARGET_CODE_BUILDER_HPP
