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

class ScalarExprEmitter {
public:
  ScalarExprEmitter(llvm::LLVMContext &, llvm::IRBuilder<> &);

  llvm::Value *EmitBinOp(const frontEnd::ASTNode *InformAST,
                         frontEnd::TokenType T, llvm::Value *L, llvm::Value *R);

  llvm::Value *EmitIntegralBinOp(const frontEnd::ASTNode *InformAST,
                                 frontEnd::TokenType T, llvm::Value *L,
                                 llvm::Value *R);

  llvm::Value *EmitFloatBinOp(const frontEnd::ASTNode *InformAST,
                              frontEnd::TokenType T, llvm::Value *L,
                              llvm::Value *R);

private:
  llvm::LLVMContext &IRCtx;
  llvm::IRBuilder<> &IRBuilder;
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_SCALAR_EXPR_EMITTER_HPP
