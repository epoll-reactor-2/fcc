/* TypeResolver.cpp - Helper class to translate frontend types to LLVM.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/TypeResolver.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "Utility/Diagnostic.h"
#include "llvm/IR/Type.h"

namespace weak {

TypeResolver::TypeResolver(llvm::IRBuilder<> &I) : mIRBuilder(I) {}

const ASTVarDecl *TypeResolver::GetVarDecl(const ASTNode *Node) {
  if (!Node->Is(AST_VAR_DECL))
    weak::CompileError(Node) << "Expected declaration";

  const auto *Decl = static_cast<const ASTVarDecl *>(Node);
  return Decl;
}

llvm::Type *TypeResolver::Resolve(TokenType T, unsigned LineNo,
                                  unsigned ColumnNo) {
  switch (T) {
  case TOK_VOID:
    return mIRBuilder.getVoidTy();
  case TOK_CHAR:
    return mIRBuilder.getInt8Ty();
  case TOK_INT:
    return mIRBuilder.getInt32Ty();
  case TOK_BOOLEAN:
    return mIRBuilder.getInt1Ty();
  case TOK_FLOAT:
    return mIRBuilder.getFloatTy();
  case TOK_STRING:
    return mIRBuilder.getInt8PtrTy();
  default:
    weak::CompileError(LineNo, ColumnNo) << "Wrong type: " << TokenToString(T);
    weak::UnreachablePoint();
  }
}

llvm::Type *TypeResolver::Resolve(TokenType T, const ASTNode *LocationAST) {
  return Resolve(T, LocationAST->LineNo(), LocationAST->ColumnNo());
}

llvm::Type *TypeResolver::Resolve(const ASTNode *Node) {
  const ASTVarDecl *Decl = GetVarDecl(Node);
  return Resolve(Decl->DataType(), Decl->LineNo(), Decl->ColumnNo());
}

llvm::Type *TypeResolver::ResolveExceptVoid(TokenType T, unsigned LineNo,
                                            unsigned ColumnNo) {
  switch (T) {
  case TOK_CHAR:
    return mIRBuilder.getInt8Ty();
  case TOK_INT:
    return mIRBuilder.getInt32Ty();
  case TOK_BOOLEAN:
    return mIRBuilder.getInt1Ty();
  case TOK_FLOAT:
    return mIRBuilder.getFloatTy();
  case TOK_STRING:
    return mIRBuilder.getInt8PtrTy();
  default:
    weak::CompileError(LineNo, ColumnNo) << "Wrong type: " << TokenToString(T);
    weak::UnreachablePoint();
  }
}

llvm::Type *TypeResolver::ResolveExceptVoid(TokenType T,
                                            const ASTNode *LocationAST) {
  return ResolveExceptVoid(T, LocationAST->LineNo(), LocationAST->ColumnNo());
}

llvm::Type *TypeResolver::ResolveExceptVoid(const ASTNode *Node) {
  const ASTVarDecl *Decl = GetVarDecl(Node);
  return ResolveExceptVoid(Decl->DataType(), Decl->LineNo(), Decl->ColumnNo());
}

} // namespace weak