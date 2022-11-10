/* TypeCheck.h - Helper functions to do type checks.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TYPE_CHECK_H
#define WEAK_COMPILER_MIDDLE_END_TYPE_CHECK_H

namespace llvm {
class Type;
class Value;
class AllocaInst;
} // namespace llvm

namespace weak {

class ASTNode;

/// Ensure that given types are same or emit compile error on mismatch.
void AssertSame(ASTNode *InformAST, llvm::Value *L, llvm::Value *R);

/// Ensure that given types are same or emit compile error on mismatch.
void AssertSame(ASTNode *InformAST, llvm::Type *L, llvm::Type *R);

/// Ensure that given index does not walk beyond the array boundary.
///
/// This is simple check for cases, when user provides array accessing by
/// constant integer, like **arr[100]**, when **arr** has size 10.
///
/// \todo: Proper check of string values also.
void AssertNotOutOfRange(ASTNode *InformAST, llvm::AllocaInst *ArrayAlloca,
                         llvm::Value *Index);

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_CHECK_H