/* TypeCheck.hpp - Helper class to do type checks.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TYPE_CHECK_HPP
#define WEAK_COMPILER_MIDDLE_END_TYPE_CHECK_HPP

#include "FrontEnd/AST/ASTNode.hpp"

namespace llvm {
class Type;
class Value;
} // namespace llvm

namespace weak {
namespace middleEnd {

/// Type checker.
class TypeCheck {
public:
  /// Ensure that given types are same or emit compile error on mismatch.
  void AssertSame(const frontEnd::ASTNode *InformAST, llvm::Value *L,
                  llvm::Value *R);
  /// Ensure that given types are same or emit compile error on mismatch.
  void AssertSame(const frontEnd::ASTNode *InformAST, llvm::Type *L,
                  llvm::Type *R);

private:
  static std::string TypeToString(llvm::Type *T);
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_CHECK_HPP