/* TypeResolver.h - Helper class to translate frontend types to LLVM.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_TYPE_RESOLVER_H
#define WEAK_COMPILER_MIDDLE_END_TYPE_RESOLVER_H

#include "FrontEnd/Lex/DataType.h"
#include "llvm/IR/IRBuilder.h"

namespace llvm {
class Type;
} // namespace llvm

namespace weak {

class ASTNode;

/// Helper class to translate trivial frontend types to LLVM.
/// Structures should be analyzed outside this class.
class TypeResolver {
public:
  TypeResolver(llvm::IRBuilder<> &);

  /// Convert given parameter (including void) to corresponding LLVM type.
  llvm::Type *Resolve(ASTNode *AST, unsigned IndirectionLvl = 0U);
  /// \copydoc TypeResolver::Resolve(ASTNode *, unsigned)
  llvm::Type *Resolve(DataType DT, unsigned IndirectionLvl = 0U);

  /// Convert given parameter (excluding void) to corresponding LLVM type.
  llvm::Type *ResolveExceptVoid(ASTNode *AST, unsigned IndirectionLvl = 0U);
  /// \copydoc TypeResolver::ResolveExceptVoid(ASTNode *, unsigned)
  llvm::Type *ResolveExceptVoid(DataType DT, unsigned IndirectionLvl = 0U);

private:
  llvm::Type *ResolveArray(ASTNode *AST, unsigned IndirectionLvl);

  /// Reference to global LLVM stuff.
  llvm::IRBuilder<> &mIRBuilder;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_RESOLVER_H