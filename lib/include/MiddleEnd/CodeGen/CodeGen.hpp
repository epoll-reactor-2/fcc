/* CodeGen.hpp - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_CODEGEN_HPP
#define WEAK_COMPILER_MIDDLE_END_CODEGEN_HPP

#include "FrontEnd/AST/ASTVisitor.hpp"
#include "MiddleEnd/Storage/DeclsStorage.hpp"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include <map>

namespace weak {

/// \brief LLVM IR generator.
///
/// Implemented as AST visitor because it still does not operates on CFG.
class CodeGen : private ASTVisitor {
public:
  CodeGen(ASTNode *TheRoot);

  /// Convert AST to LLVM IR starting from root node (usually CompoundStmt).
  void CreateCode();

  llvm::Module &GetModule();

  /// Get list of already created global variables.
  const llvm::SymbolTableList<llvm::GlobalVariable> &GetGlobalVariables() const;

  /// Get list of already created functions.
  const llvm::SymbolTableList<llvm::Function> &GetGlobalFunctions() const;

  /// Create and get visual representation.
  std::string ToString() const;

private:
  // Literals.
  void Visit(const ASTBooleanLiteral *) override;
  void Visit(const ASTCharLiteral *) override;
  void Visit(const ASTIntegerLiteral *) override;
  void Visit(const ASTFloatingPointLiteral *) override;
  void Visit(const ASTStringLiteral *) override;

  // Operators.
  void Visit(const ASTBinaryOperator *) override;
  void Visit(const ASTUnaryOperator *) override;

  // Inside-loop statements.
  void Visit(const ASTBreakStmt *) override {}
  void Visit(const ASTContinueStmt *) override {}

  // Loop statements.
  void Visit(const ASTForStmt *) override;
  void Visit(const ASTWhileStmt *) override;
  void Visit(const ASTDoWhileStmt *) override;

  // Condition statements.
  void Visit(const ASTIfStmt *) override;

  // Function statements.
  void Visit(const ASTFunctionDecl *) override;
  void Visit(const ASTFunctionCall *) override;
  void Visit(const ASTFunctionPrototype *) override;

  // Declarations.
  void Visit(const ASTArrayDecl *) override;
  void Visit(const ASTVarDecl *) override;
  void Visit(const ASTStructDecl *) override {}

  // The rest.
  void Visit(const ASTArrayAccess *) override;
  void Visit(const ASTSymbol *) override;
  void Visit(const ASTCompoundStmt *) override;
  void Visit(const ASTReturnStmt *) override;

  /// Analyzed root AST node.
  ASTNode *Root;
  /// Variables pool.
  DeclsStorage DeclStorage;
  /// Consequence of using visitor pattern, since we cannot return anything from
  /// visit functions.
  llvm::Value *LastInstr;
  /// This is needed because there are two contexts of usage of array values:
  /// 1) array element is reassigned;
  /// 2) array element is accessed.
  ///
  /// So we store pointer to array element there, and the value itself normally
  /// in LastInstr.
  llvm::Value *LastArrayPtr;
  /// LLVM stuff.
  llvm::LLVMContext IRCtx;
  /// LLVM stuff.
  llvm::Module IRModule;
  /// LLVM stuff.
  llvm::IRBuilder<> IRBuilder;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_CODEGEN_HPP