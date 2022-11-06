/* ScalarExprEmitter.cpp - Generator of operations on numeric data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/ScalarExprEmitter.h"
#include "FrontEnd/Lex/Token.h"
#include "Utility/Diagnostic.h"
#include "llvm/IR/Value.h"

static std::string TypeToString(llvm::Type *T) {
  std::string Type;
  llvm::raw_string_ostream Stream(Type);
  T->print(Stream);
  return Stream.str();
}

namespace weak {

ScalarExprEmitter::ScalarExprEmitter(llvm::IRBuilder<> &I) : mIRBuilder(I) {}

llvm::Value *ScalarExprEmitter::EmitBinOp(const ASTNode *InformAST, TokenType T,
                                          llvm::Value *L, llvm::Value *R) {
  assert(L->getType() == R->getType());

  if (L->getType()->isIntegerTy())
    return EmitIntegralBinOp(InformAST, T, L, R);

  if (L->getType()->isFloatTy())
    return EmitFloatBinOp(InformAST, T, L, R);

  weak::CompileError(InformAST)
      << "Cannot emit binary instruction, invalid operands: "
      << TypeToString(L->getType()) << " and " << TypeToString(R->getType());
  Unreachable();
}

llvm::Value *ScalarExprEmitter::EmitIntegralBinOp(const ASTNode *InformAST,
                                                  TokenType T, llvm::Value *L,
                                                  llvm::Value *R) {
  switch (T) {
  case TOK_PLUS:
    return mIRBuilder.CreateAdd(L, R);
  case TOK_MINUS:
    return mIRBuilder.CreateSub(L, R);
  case TOK_STAR:
    return mIRBuilder.CreateMul(L, R);
  case TOK_SLASH:
    return mIRBuilder.CreateSDiv(L, R);
  case TOK_LE:
    return mIRBuilder.CreateICmpSLE(L, R);
  case TOK_LT:
    return mIRBuilder.CreateICmpSLT(L, R);
  case TOK_GE:
    return mIRBuilder.CreateICmpSGE(L, R);
  case TOK_GT:
    return mIRBuilder.CreateICmpSGT(L, R);
  case TOK_EQ:
    return mIRBuilder.CreateICmpEQ(L, R);
  case TOK_NEQ:
    return mIRBuilder.CreateICmpNE(L, R);
  case TOK_OR:
    return mIRBuilder.CreateLogicalOr(L, R);
  case TOK_AND:
    return mIRBuilder.CreateLogicalAnd(L, R);
  case TOK_BIT_OR:
    return mIRBuilder.CreateOr(L, R);
  case TOK_BIT_AND:
    return mIRBuilder.CreateAnd(L, R);
  case TOK_XOR:
    return mIRBuilder.CreateXor(L, R);
  case TOK_SHL:
    return mIRBuilder.CreateShl(L, R);
  case TOK_SHR:
    return mIRBuilder.CreateAShr(L, R);
  default:
    weak::CompileError(InformAST)
        << "Cannot apply `" << weak::TokenToString(T) << "` to integers";
    Unreachable();
  } // switch
}

llvm::Value *ScalarExprEmitter::EmitFloatBinOp(const ASTNode *InformAST,
                                               TokenType T, llvm::Value *L,
                                               llvm::Value *R) {
  switch (T) {
  case TOK_PLUS:
    return mIRBuilder.CreateFAdd(L, R);
  case TOK_MINUS:
    return mIRBuilder.CreateFSub(L, R);
  case TOK_STAR:
    return mIRBuilder.CreateFMul(L, R);
  case TOK_SLASH:
    return mIRBuilder.CreateFDiv(L, R);
  case TOK_LE:
    return mIRBuilder.CreateFCmpOLE(L, R);
  case TOK_LT:
    return mIRBuilder.CreateFCmpOLT(L, R);
  case TOK_GE:
    return mIRBuilder.CreateFCmpOGE(L, R);
  case TOK_GT:
    return mIRBuilder.CreateFCmpOGT(L, R);
  case TOK_EQ:
    return mIRBuilder.CreateFCmpOEQ(L, R);
  case TOK_NEQ:
    return mIRBuilder.CreateFCmpONE(L, R);
  case TOK_OR:
    return mIRBuilder.CreateLogicalOr(L, R);
  case TOK_AND:
    return mIRBuilder.CreateLogicalAnd(L, R);
  default:
    weak::CompileError(InformAST)
        << "Cannot apply `" << TokenToString(T) << "` to floats";
    Unreachable();
  } // switch
}

} // namespace weak