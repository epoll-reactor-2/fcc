/* ScalarExprEmitter.hpp - Generator of operations on numeric data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_SCALAR_EXPR_EMITTER_HPP
#define WEAK_COMPILER_MIDDLE_END_SCALAR_EXPR_EMITTER_HPP

#include "FrontEnd/Lex/Token.hpp"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"

namespace llvm {
class Value;
} // namespace llvm

namespace weak {
namespace frontEnd {
class ASTNode;
} // namespace frontEnd
} // namespace weak

namespace weak {
namespace middleEnd {

/// Generator of operations on numeric data types.
class ScalarExprEmitter {
public:
  ScalarExprEmitter(llvm::LLVMContext &, llvm::IRBuilder<> &);

  /// Emit operation supported by integral or floating points.
  ///
  /// \note
  ///         - Set of supported operations is depend on given L and R types.
  ///         - Requires same LLVM types.
  /// \param  InformAST AST node of expression. Used to emit localized error
  ///                   messages.
  /// \param  T         Operation to be emitted.
  /// \param  L         Left operand.
  /// \param  R         Right operand.
  /// \return           Created operation.
  llvm::Value *EmitBinOp(const frontEnd::ASTNode *InformAST,
                         frontEnd::TokenType T, llvm::Value *L, llvm::Value *R);

  /// Emit operation supported only by integral type.
  ///
  /// \note   Requires same LLVM types.
  /// \param  InformAST AST node of expression. Used to emit localized error
  ///                   messages.
  /// \param  T         Operation to be emitted.
  /// \param  L         Left operand.
  /// \param  R         Right operand.
  /// \return           Created operation.
  llvm::Value *EmitIntegralBinOp(const frontEnd::ASTNode *InformAST,
                                 frontEnd::TokenType T, llvm::Value *L,
                                 llvm::Value *R);

  /// Emit operation supported only by floating points.
  ///
  /// \note   Requires same LLVM types.
  /// \param  InformAST AST node of expression. Used to emit localized error
  ///                   messages.
  /// \param  T         Operation to be emitted.
  /// \param  L         Left operand.
  /// \param  R         Right operand.
  /// \return           Created operation.
  llvm::Value *EmitFloatBinOp(const frontEnd::ASTNode *InformAST,
                              frontEnd::TokenType T, llvm::Value *L,
                              llvm::Value *R);

private:
  /// Reference to global LLVM stuff.
  llvm::LLVMContext &IRCtx;
  /// Reference to global LLVM stuff.
  llvm::IRBuilder<> &IRBuilder;
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_SCALAR_EXPR_EMITTER_HPP
