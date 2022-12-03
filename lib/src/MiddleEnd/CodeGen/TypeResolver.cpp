/* TypeResolver.cpp - Helper class to translate frontend types to LLVM.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/TypeResolver.h"
#include "FrontEnd/AST/ASTArrayDecl.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "Utility/EnumOstreamOperators.h"
#include "Utility/Unreachable.h"
#include "llvm/IR/Type.h"

namespace weak {

static DataType DeclType(ASTNode *Node) {
  if (Node->Is(AST_VAR_DECL))
    return static_cast<ASTVarDecl *>(Node)->DataType();

  if (Node->Is(AST_ARRAY_DECL))
    return static_cast<ASTArrayDecl *>(Node)->DataType();

  Unreachable();
}

TypeResolver::TypeResolver(llvm::IRBuilder<> &I)
  : mIRBuilder(I) {}

llvm::Type *TypeResolver::Resolve(DataType T) {
  switch (T) {
  case DT_VOID:   return mIRBuilder.getVoidTy();
  case DT_CHAR:   return mIRBuilder.getInt8Ty();
  case DT_INT:    return mIRBuilder.getInt32Ty();
  case DT_BOOL:   return mIRBuilder.getInt1Ty();
  case DT_FLOAT:  return mIRBuilder.getFloatTy();
  case DT_STRING: return mIRBuilder.getInt8PtrTy();
  default:        Unreachable();
  }
}

llvm::Type *TypeResolver::Resolve(ASTNode *AST) {
  if (!AST->Is(AST_ARRAY_DECL))
    return Resolve(DeclType(AST));

  return ResolveArray(AST);
}

llvm::Type *TypeResolver::ResolveExceptVoid(DataType T) {
  switch (T) {
  case DT_CHAR:   return mIRBuilder.getInt8Ty();
  case DT_INT:    return mIRBuilder.getInt32Ty();
  case DT_BOOL:   return mIRBuilder.getInt1Ty();
  case DT_FLOAT:  return mIRBuilder.getFloatTy();
  case DT_STRING: return mIRBuilder.getInt8PtrTy();
  default:        Unreachable();
  }
}

llvm::Type *TypeResolver::ResolveExceptVoid(ASTNode *AST) {
  if (!AST->Is(AST_ARRAY_DECL))
    return ResolveExceptVoid(DeclType(AST));

  return ResolveArray(AST);
}

llvm::Type *TypeResolver::ResolveArray(ASTNode *AST) {
  auto *Decl = static_cast<ASTArrayDecl *>(AST);
  const auto &ArityList = Decl->ArityList();
  assert(!ArityList.empty());

  llvm::ArrayType *ArrayTy =
    llvm::ArrayType::get(
      ResolveExceptVoid(Decl->DataType()),
      ArityList.back()
    );

  for (size_t I{ArityList.size() - 1}; I != 0; --I) {
    ArrayTy = llvm::ArrayType::get(
      ArrayTy,
      ArityList[I]
    );
  }

  return ArrayTy;
}

} // namespace weak