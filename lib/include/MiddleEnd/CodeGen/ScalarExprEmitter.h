/* ScalarExprEmitter.h - Generator of operations on numeric data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_SCALAR_EXPR_EMITTER_H
#define WEAK_COMPILER_MIDDLE_END_SCALAR_EXPR_EMITTER_H

#include "FrontEnd/Lex/TokenType.h"
#include "llvm/IR/IRBuilder.h"

namespace llvm {
class Value;
} // namespace llvm

namespace weak {

/// Generator of operations on numeric data types.
class ScalarExprEmitter {
public:
  ScalarExprEmitter(llvm::IRBuilder<> &);

  /// Emit operation supported by integral or floating points.
  ///
  /// \note
  ///         - Set of supported operations is depend on given L and R types.
  ///         - Requires same LLVM types.
  /// \param  T         Operation to be emitted.
  /// \param  L         Left operand.
  /// \param  R         Right operand.
  /// \return           Created operation.
  llvm::Value *EmitBinOp(TokenType T, llvm::Value *L, llvm::Value *R);

  /// Emit operation supported only by integral type.
  ///
  /// \note   Requires same LLVM types.
  /// \param  T         Operation to be emitted.
  /// \param  L         Left operand.
  /// \param  R         Right operand.
  /// \return           Created operation.
  llvm::Value *EmitIntegralBinOp(TokenType T, llvm::Value *L, llvm::Value *R);

  /// Emit operation supported only by floating points.
  ///
  /// \note   Requires same LLVM types.
  /// \param  T         Operation to be emitted.
  /// \param  L         Left operand.
  /// \param  R         Right operand.
  /// \return           Created operation.
  llvm::Value *EmitFloatBinOp(TokenType T, llvm::Value *L, llvm::Value *R);

private:
  /// Reference to global LLVM stuff.
  llvm::IRBuilder<> &mIRBuilder;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_SCALAR_EXPR_EMITTER_H