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

/// Helper class to translate frontend types to LLVM.
class TypeResolver {
public:
  TypeResolver(llvm::IRBuilder<> &);

  /// Convert given parameter (including void) to corresponding LLVM type.
  llvm::Type *Resolve(ASTNode *);
  /// \copydoc TypeResolver::Resolve(ASTNode *)
  llvm::Type *Resolve(DataType);

  /// Convert given parameter (excluding void) to corresponding LLVM type.
  llvm::Type *ResolveExceptVoid(ASTNode *LocationAST);
  /// \copydoc TypeResolver::ResolveExceptVoid(ASTNode *)
  llvm::Type *ResolveExceptVoid(DataType);

private:
  /// Reference to global LLVM stuff.
  llvm::IRBuilder<> &mIRBuilder;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_TYPE_RESOLVER_H