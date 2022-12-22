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

namespace weak {

static DataType DeclType(ASTNode *Node) {
  if (Node->Is(AST_VAR_DECL))
    return static_cast<ASTVarDecl *>(Node)->DataType();

  if (Node->Is(AST_ARRAY_DECL))
    return static_cast<ASTArrayDecl *>(Node)->DataType();

  Unreachable("Expected variable or array.");
}

TypeResolver::TypeResolver(llvm::IRBuilder<> &I)
  : mIRBuilder(I) {}

llvm::Type *TypeResolver::Resolve(DataType DT, unsigned IndirectionLvl) {
  llvm::Type *Ty = nullptr;
  switch (DT) {
  case DT_VOID:   Ty = mIRBuilder.getVoidTy(); break;
  case DT_CHAR:   Ty = mIRBuilder.getInt8Ty(); break;
  case DT_INT:    Ty = mIRBuilder.getInt32Ty(); break;
  case DT_BOOL:   Ty = mIRBuilder.getInt1Ty(); break;
  case DT_FLOAT:  Ty = mIRBuilder.getFloatTy(); break;
  case DT_STRING: Ty = mIRBuilder.getInt8PtrTy(); break;
  default:        Unreachable("Expected data type.");
  }
  for (unsigned I = 0U; I < IndirectionLvl; ++I)
    Ty = llvm::PointerType::get(Ty, /*AddressSpace=*/0U);
  return Ty;
}

llvm::Type *TypeResolver::Resolve(ASTNode *AST, unsigned IndirectionLvl) {
  if (!AST->Is(AST_ARRAY_DECL))
    return Resolve(DeclType(AST), IndirectionLvl);

  return ResolveArray(AST, IndirectionLvl);
}

llvm::Type *TypeResolver::ResolveExceptVoid(DataType DT, unsigned IndirectionLvl) {
  llvm::Type *Ty = nullptr;
  switch (DT) {
  case DT_CHAR:   Ty = mIRBuilder.getInt8Ty(); break;
  case DT_INT:    Ty = mIRBuilder.getInt32Ty(); break;
  case DT_BOOL:   Ty = mIRBuilder.getInt1Ty(); break;
  case DT_FLOAT:  Ty = mIRBuilder.getFloatTy(); break;
  case DT_STRING: Ty = mIRBuilder.getInt8PtrTy(); break;
  default:        Unreachable("Expected data type except void.");
  }
  for (unsigned I = 0U; I < IndirectionLvl; ++I)
    Ty = llvm::PointerType::get(Ty, /*AddressSpace=*/0U);
  return Ty;
}

llvm::Type *TypeResolver::ResolveExceptVoid(ASTNode *AST, unsigned IndirectionLvl) {
  if (!AST->Is(AST_ARRAY_DECL))
    return ResolveExceptVoid(DeclType(AST), IndirectionLvl);

  return ResolveArray(AST, IndirectionLvl);
}

llvm::Type *TypeResolver::ResolveArray(ASTNode *AST, unsigned IndirectionLvl) {
  auto *Decl = static_cast<ASTArrayDecl *>(AST);
  const auto &ArityList = Decl->ArityList();
  assert(!ArityList.empty());
  auto It = ArityList.rbegin();

  llvm::Type *Ty =
    llvm::ArrayType::get(
      ResolveExceptVoid(Decl->DataType()),
      *It++
    );

  while (It != ArityList.rend())
    Ty = llvm::ArrayType::get(
      Ty,
      *It++
    );

  for (unsigned I = 0U; I < IndirectionLvl; ++I)
    Ty = llvm::PointerType::get(Ty, /*AddressSpace=*/0U);

  return Ty;
}

} // namespace weak