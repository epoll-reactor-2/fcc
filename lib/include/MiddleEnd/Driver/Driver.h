/* Driver.h - Builder of executable code from LLVM IR.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_DRIVER_H
#define WEAK_COMPILER_MIDDLE_END_DRIVER_H

#include <string>

namespace llvm {
class Module;
} // namespace llvm

namespace weak {

/// Builder of executable code from LLVM IR.
class Driver {
public:
  Driver(llvm::Module &M, std::string_view OutPath);

  /// Compile LLVM IR to object code and write it to output file.
  ///
  /// \note In debugging purposes this function uses clang to somehow emit
  ///       executable file.
  /// \todo Judge how properly do emitting of binaries without bash stubs.
  void Compile();

private:
  /// Reference to global LLVM stuff.
  llvm::Module &mIRModule;
  /// Reference to global LLVM stuff.
  std::string mOutPath;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_DRIVER_H