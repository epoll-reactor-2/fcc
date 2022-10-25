/* TypeResolver.cpp - Helper class to translate frontend types to LLVM.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/TypeResolver.hpp"
#include "FrontEnd/AST/ASTVarDecl.hpp"
#include "Utility/Diagnostic.hpp"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Type.h"

namespace weak {

TypeResolver::TypeResolver(llvm::LLVMContext &TheLLVMCtx)
    : LLVMCtx(TheLLVMCtx) {}

const ASTVarDecl *TypeResolver::GetVarDecl(const ASTNode *Node) {
  if (Node->GetASTType() != ASTType::VAR_DECL)
    weak::CompileError(Node) << "Expected parameter";

  const auto *Decl = static_cast<const ASTVarDecl *>(Node);
  return Decl;
}

llvm::Type *TypeResolver::Resolve(TokenType T, unsigned LineNo,
                                  unsigned ColumnNo) {
  switch (T) {
  case TOK_VOID:
    return llvm::Type::getVoidTy(LLVMCtx);
  case TOK_CHAR:
    return llvm::Type::getInt8Ty(LLVMCtx);
  case TOK_INT:
    return llvm::Type::getInt32Ty(LLVMCtx);
  case TOK_BOOLEAN:
    return llvm::Type::getInt1Ty(LLVMCtx);
  case TOK_FLOAT:
    return llvm::Type::getFloatTy(LLVMCtx);
  case TOK_STRING:
    return llvm::Type::getInt8PtrTy(LLVMCtx);
  default:
    weak::CompileError(LineNo, ColumnNo) << "Wrong type: " << TokenToString(T);
    weak::UnreachablePoint();
  }
}

llvm::Type *TypeResolver::Resolve(const ASTNode *Node) {
  const ASTVarDecl *Decl = GetVarDecl(Node);
  return Resolve(Decl->GetDataType(), Decl->GetLineNo(), Decl->GetColumnNo());
}

llvm::Type *TypeResolver::ResolveExceptVoid(TokenType T, unsigned LineNo,
                                            unsigned ColumnNo) {
  switch (T) {
  case TOK_CHAR:
    return llvm::Type::getInt8Ty(LLVMCtx);
  case TOK_INT:
    return llvm::Type::getInt32Ty(LLVMCtx);
  case TOK_FLOAT:
    return llvm::Type::getFloatTy(LLVMCtx);
  case TOK_BOOLEAN:
    return llvm::Type::getInt1Ty(LLVMCtx);
  case TOK_STRING:
    return llvm::Type::getInt8PtrTy(LLVMCtx);
  default:
    weak::CompileError(LineNo, ColumnNo) << "Wrong type: " << TokenToString(T);
    weak::UnreachablePoint();
  }
}

llvm::Type *TypeResolver::ResolveExceptVoid(const ASTNode *Node) {
  const ASTVarDecl *Decl = GetVarDecl(Node);
  return ResolveExceptVoid(Decl->GetDataType(), Decl->GetLineNo(),
                           Decl->GetColumnNo());
}

} // namespace weak