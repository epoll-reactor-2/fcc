/* TypeResolver.cpp - Helper class to translate frontend types to LLVM.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/TypeResolver.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/Lex/Token.h"
#include "Utility/Diagnostic.h"
#include "llvm/IR/Type.h"

namespace weak {

static ASTVarDecl *GetVarDecl(ASTNode *Node) {
  if (!Node->Is(AST_VAR_DECL))
    weak::CompileError(Node) << "Expected declaration";

  return static_cast<ASTVarDecl *>(Node);
}

TypeResolver::TypeResolver(llvm::IRBuilder<> &I) : mIRBuilder(I) {}

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
    Unreachable();
  }
}

llvm::Type *TypeResolver::Resolve(TokenType T, ASTNode *LocationAST) {
  return Resolve(T, LocationAST->LineNo(), LocationAST->ColumnNo());
}

llvm::Type *TypeResolver::Resolve(ASTNode *LocationAST) {
  ASTVarDecl *Decl = GetVarDecl(LocationAST);
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
    Unreachable();
  }
}

llvm::Type *TypeResolver::ResolveExceptVoid(TokenType T, ASTNode *LocationAST) {
  return ResolveExceptVoid(T, LocationAST->LineNo(), LocationAST->ColumnNo());
}

llvm::Type *TypeResolver::ResolveExceptVoid(ASTNode *LocationAST) {
  ASTVarDecl *Decl = GetVarDecl(LocationAST);
  return ResolveExceptVoid(Decl->DataType(), Decl->LineNo(), Decl->ColumnNo());
}

} // namespace weak