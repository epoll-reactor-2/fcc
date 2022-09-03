/* TypeCheck.cpp - Helper class to do type checks.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/TypeCheck.hpp"
#include "Utility/Diagnostic.hpp"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"

namespace weak {
namespace middleEnd {

void TypeCheck::AssertSame(const frontEnd::ASTNode *InformAST, llvm::Value *L,
                           llvm::Value *R) {
  AssertSame(InformAST, L->getType(), R->getType());
}

void TypeCheck::AssertSame(const frontEnd::ASTNode *InformAST, llvm::Type *L,
                           llvm::Type *R) {
  if (L == R)
    return;

  weak::CompileError(InformAST)
      << "Type mismatch: " << TypeToString(L) << " and " << TypeToString(R);
}

std::string TypeCheck::TypeToString(llvm::Type *T) {
  std::string Type;
  llvm::raw_string_ostream Stream(Type);
  T->print(Stream);
  return Stream.str();
}

} // namespace middleEnd
} // namespace weak