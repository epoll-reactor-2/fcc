/* ScalarExprEmitter.cpp - Generator of operations on numeric data types.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/ScalarExprEmitter.hpp"
#include "Utility/Diagnostic.hpp"
#include "llvm/IR/Value.h"

namespace weak {
namespace middleEnd {

ScalarExprEmitter::ScalarExprEmitter(llvm::LLVMContext &TheIRCtx,
                                     llvm::IRBuilder<> &TheIRBuilder)
    : IRCtx(TheIRCtx), IRBuilder(TheIRBuilder) {}

llvm::Value *ScalarExprEmitter::EmitBinOp(const frontEnd::ASTNode *InformAST,
                                          frontEnd::TokenType T, llvm::Value *L,
                                          llvm::Value *R) {
  bool IsFloatOperands = L->getType() == llvm::Type::getFloatTy(IRCtx);
  bool IsIntegralOperands = false;
  IsIntegralOperands |= (L->getType() == llvm::Type::getInt1Ty(IRCtx));
  IsIntegralOperands |= (L->getType() == llvm::Type::getInt8Ty(IRCtx));
  IsIntegralOperands |= (L->getType() == llvm::Type::getInt16Ty(IRCtx));
  IsIntegralOperands |= (L->getType() == llvm::Type::getInt32Ty(IRCtx));
  IsIntegralOperands |= (L->getType() == llvm::Type::getInt64Ty(IRCtx));
  IsIntegralOperands |= (L->getType() == llvm::Type::getInt128Ty(IRCtx));

  if (IsIntegralOperands)
    return EmitIntegralBinOp(InformAST, T, L, R);

  if (IsFloatOperands)
    return EmitFloatBinOp(InformAST, T, L, R);

  weak::UnreachablePoint(
      "ScalarExprEmitter::EmitRegularBinOp: Invalid operands passed");
}

llvm::Value *
ScalarExprEmitter::EmitIntegralBinOp(const frontEnd::ASTNode *InformAST,
                                     frontEnd::TokenType T, llvm::Value *L,
                                     llvm::Value *R) {
  using frontEnd::TokenType;
  switch (T) {
  case TokenType::PLUS:
    return IRBuilder.CreateAdd(L, R);
  case TokenType::MINUS:
    return IRBuilder.CreateSub(L, R);
  case TokenType::STAR:
    return IRBuilder.CreateMul(L, R);
  case TokenType::SLASH:
    return IRBuilder.CreateSDiv(L, R);
  case TokenType::LE:
    return IRBuilder.CreateICmpSLE(L, R);
  case TokenType::LT:
    return IRBuilder.CreateICmpSLT(L, R);
  case TokenType::GE:
    return IRBuilder.CreateICmpSGE(L, R);
  case TokenType::GT:
    return IRBuilder.CreateICmpSGT(L, R);
  case TokenType::EQ:
    return IRBuilder.CreateICmpEQ(L, R);
  case TokenType::NEQ:
    return IRBuilder.CreateICmpNE(L, R);
  case TokenType::OR:
    return IRBuilder.CreateLogicalOr(L, R);
  case TokenType::AND:
    return IRBuilder.CreateLogicalAnd(L, R);
  case TokenType::BIT_OR:
    return IRBuilder.CreateOr(L, R);
  case TokenType::BIT_AND:
    return IRBuilder.CreateAnd(L, R);
  case TokenType::XOR:
    return IRBuilder.CreateXor(L, R);
  case TokenType::SHL:
    return IRBuilder.CreateShl(L, R);
  case TokenType::SHR:
    return IRBuilder.CreateAShr(L, R);
  default:
    weak::CompileError(InformAST)
        << "Cannot apply `" << weak::frontEnd::TokenToString(T)
        << "` to integers";
    weak::UnreachablePoint();
  } // switch
}

llvm::Value *
ScalarExprEmitter::EmitFloatBinOp(const frontEnd::ASTNode *InformAST,
                                  frontEnd::TokenType T, llvm::Value *L,
                                  llvm::Value *R) {
  using frontEnd::TokenType;
  switch (T) {
  case TokenType::PLUS:
    return IRBuilder.CreateFAdd(L, R);
  case TokenType::MINUS:
    return IRBuilder.CreateFSub(L, R);
  case TokenType::STAR:
    return IRBuilder.CreateFMul(L, R);
  case TokenType::SLASH:
    return IRBuilder.CreateFDiv(L, R);
  case TokenType::LE:
    return IRBuilder.CreateFCmpOLE(L, R);
  case TokenType::LT:
    return IRBuilder.CreateFCmpOLT(L, R);
  case TokenType::GE:
    return IRBuilder.CreateFCmpOGE(L, R);
  case TokenType::GT:
    return IRBuilder.CreateFCmpOGT(L, R);
  case TokenType::EQ:
    return IRBuilder.CreateFCmpOEQ(L, R);
  case TokenType::NEQ:
    return IRBuilder.CreateFCmpONE(L, R);
  default:
    weak::CompileError(InformAST)
        << "Cannot apply `" << weak::frontEnd::TokenToString(T)
        << "` to floats";
    weak::UnreachablePoint();
  } // switch
}

} // namespace middleEnd
} // namespace weak