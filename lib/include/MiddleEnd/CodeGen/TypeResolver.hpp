/* TypeResolver.hpp - Helper class to translate frontend types to LLVM.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TYPE_RESOLVER_HPP
#define WEAK_COMPILER_MIDDLE_END_TYPE_RESOLVER_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/AST/ASTVarDecl.hpp"
#include "FrontEnd/Lex/Token.hpp"

namespace llvm {
class LLVMContext;
class Type;
} // namespace llvm

namespace weak {

/// Helper class to translate frontend types to LLVM.
class TypeResolver {
public:
  TypeResolver(llvm::LLVMContext &);

  /// Convert given parameter (including void) to corresponding LLVM type.
  llvm::Type *Resolve(TokenType, unsigned LineNo = 0U, unsigned ColumnNo = 0U);
  /// \copydoc TypeResolver::Resolve(TokenType, unsigned, unsigned)
  llvm::Type *Resolve(const ASTNode *);

  /// Convert given parameter (excluding void) to corresponding LLVM type.
  llvm::Type *ResolveExceptVoid(TokenType, unsigned LineNo = 0U,
                                unsigned ColumnNo = 0U);
  /// \copydoc TypeResolver::ResolveExceptVoid(TokenType, unsigned,
  /// unsigned)
  llvm::Type *ResolveExceptVoid(const ASTNode *);

private:
  /// Convert ASTNode to ASTVarDecl, or
  /// emit compile error on conversion error.
  const ASTVarDecl *GetVarDecl(const ASTNode *);

  /// Reference to global LLVM stuff.
  llvm::LLVMContext &LLVMCtx;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_RESOLVER_HPP