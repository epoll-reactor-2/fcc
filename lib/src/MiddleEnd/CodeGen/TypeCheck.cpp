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

void TypeCheck::AssertSame(const frontEnd::ASTNode *Node, llvm::Value *L,
                           llvm::Value *R) {
  if (L->getType() == R->getType())
    return;

  unsigned LineNo = Node->GetLineNo();
  unsigned ColumnNo = Node->GetColumnNo();
  weak::CompileError(LineNo, ColumnNo)
      << "Type mismatch: " << TypeToString(L->getType()) << " and "
      << TypeToString(R->getType());
}

std::string TypeCheck::TypeToString(llvm::Type *T) {
  std::string Type;
  llvm::raw_string_ostream Stream(Type);
  T->print(Stream);
  return Stream.str();
}

} // namespace middleEnd
} // namespace weak