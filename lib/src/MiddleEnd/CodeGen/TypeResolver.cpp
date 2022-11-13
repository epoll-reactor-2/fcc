/* TypeResolver.cpp - Helper class to translate frontend types to LLVM.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/TypeResolver.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/Lex/Token.h"
#include "Utility/Diagnostic.h"
#include "Utility/EnumOstreamOperators.h"
#include "llvm/IR/Type.h"

namespace weak {

static ASTVarDecl *GetVarDecl(ASTNode *Node) {
  if (!Node->Is(AST_VAR_DECL))
    weak::CompileError(Node) << "Expected declaration";

  return static_cast<ASTVarDecl *>(Node);
}

TypeResolver::TypeResolver(llvm::IRBuilder<> &I) : mIRBuilder(I) {}

llvm::Type *TypeResolver::Resolve(DataType T, unsigned LineNo,
                                  unsigned ColumnNo) {
  switch (T) {
  case DT_VOID:
    return mIRBuilder.getVoidTy();
  case DT_CHAR:
    return mIRBuilder.getInt8Ty();
  case DT_INT:
    return mIRBuilder.getInt32Ty();
  case DT_BOOL:
    return mIRBuilder.getInt1Ty();
  case DT_FLOAT:
    return mIRBuilder.getFloatTy();
  case DT_STRING:
    return mIRBuilder.getInt8PtrTy();
  default:
    weak::CompileError(LineNo, ColumnNo) << "Wrong type: " << T;
    Unreachable();
  }
}

llvm::Type *TypeResolver::Resolve(DataType T, ASTNode *LocationAST) {
  return Resolve(T, LocationAST->LineNo(), LocationAST->ColumnNo());
}

llvm::Type *TypeResolver::Resolve(ASTNode *LocationAST) {
  ASTVarDecl *Decl = GetVarDecl(LocationAST);
  return Resolve(Decl->DataType(), Decl->LineNo(), Decl->ColumnNo());
}

llvm::Type *TypeResolver::ResolveExceptVoid(DataType T, unsigned LineNo,
                                            unsigned ColumnNo) {
  switch (T) {
  case DT_CHAR:
    return mIRBuilder.getInt8Ty();
  case DT_INT:
    return mIRBuilder.getInt32Ty();
  case DT_BOOL:
    return mIRBuilder.getInt1Ty();
  case DT_FLOAT:
    return mIRBuilder.getFloatTy();
  case DT_STRING:
    return mIRBuilder.getInt8PtrTy();
  default:
    weak::CompileError(LineNo, ColumnNo) << "Wrong type: " << T;
    Unreachable();
  }
}

llvm::Type *TypeResolver::ResolveExceptVoid(DataType T, ASTNode *LocationAST) {
  return ResolveExceptVoid(T, LocationAST->LineNo(), LocationAST->ColumnNo());
}

llvm::Type *TypeResolver::ResolveExceptVoid(ASTNode *LocationAST) {
  ASTVarDecl *Decl = GetVarDecl(LocationAST);
  return ResolveExceptVoid(Decl->DataType(), Decl->LineNo(), Decl->ColumnNo());
}

} // namespace weak