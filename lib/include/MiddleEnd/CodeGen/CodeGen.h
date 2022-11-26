/* CodeGen.h - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_CODEGEN_H
#define WEAK_COMPILER_MIDDLE_END_CODEGEN_H

#include "FrontEnd/AST/ASTVisitor.h"
#include "MiddleEnd/Storage/Storage.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

namespace weak {

/// \brief LLVM IR generator.
///
/// \note Requires analyzed by weak::Sema AST.
///
/// Implemented as AST visitor because it still does not operates on CFG.
class CodeGen : private ASTVisitor {
public:
  CodeGen(ASTNode *Root);

  /// Convert AST to LLVM IR starting from root node (usually CompoundStmt).
  void CreateCode();

  llvm::Module &Module();

  /// Get list of already created global variables.
  const llvm::SymbolTableList<llvm::GlobalVariable> &GlobalVariables() const;

  /// Get list of already created functions.
  const llvm::SymbolTableList<llvm::Function> &GlobalFunctions() const;

  std::vector<llvm::StructType *> Types() const;

  /// Create and get visual representation.
  std::string ToString() const;

private:
  // Literals.
  void Visit(ASTBool *) override;
  void Visit(ASTChar *) override;
  void Visit(ASTNumber *) override;
  void Visit(ASTFloat *) override;
  void Visit(ASTString *) override;

  // Operators.
  void Visit(ASTBinary *) override;
  void Visit(ASTUnary *) override;

  // Inside-loop statements.
  void Visit(ASTBreak *) override {}
  void Visit(ASTContinue *) override {}

  // Loop statements.
  void Visit(ASTFor *) override;
  void Visit(ASTWhile *) override;
  void Visit(ASTDoWhile *) override;

  // Condition statements.
  void Visit(ASTIf *) override;

  // Function statements.
  void Visit(ASTFunctionDecl *) override;
  void Visit(ASTFunctionCall *) override;
  void Visit(ASTFunctionPrototype *) override;

  // Declarations.
  void Visit(ASTArrayDecl *) override;
  void Visit(ASTVarDecl *) override;
  void Visit(ASTStructDecl *) override;

  // The rest.
  void Visit(ASTArrayAccess *) override;
  void Visit(ASTSymbol *) override;
  void Visit(ASTCompound *) override;
  void Visit(ASTReturn *) override;
  void Visit(ASTMemberAccess *) override;

  /// Analyzed root AST node.
  ASTNode *mRoot;
  /// Variables pool.
  Storage mStorage;
  /// Consequence of using visitor pattern, since we cannot return anything from
  /// visit functions.
  llvm::Value *mLastInstr;
  /// LLVM stuff.
  llvm::LLVMContext mIRCtx;
  /// LLVM stuff.
  llvm::Module mIRModule;
  /// LLVM stuff.
  llvm::IRBuilder<> mIRBuilder;

  using StructVarName = std::string;
  using TypeName = std::string;
  std::unordered_map<StructVarName, TypeName> mStructVarsStorage;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_CODEGEN_H