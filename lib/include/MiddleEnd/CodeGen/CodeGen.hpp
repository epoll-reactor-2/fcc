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
namespace middleEnd {

/// LLVM IR generator.
///
/// Implemented as AST visitor because it still does not operates on CFG.
class CodeGen : private frontEnd::ASTVisitor {
public:
  CodeGen(frontEnd::ASTNode *TheRoot);

  /// Convert AST to LLVM IR starting from root node (usually CompoundStmt).
  void CreateCode();

  llvm::Module &GetModule();

  const llvm::SymbolTableList<llvm::GlobalVariable> &GetGlobalVariables() const;

  const llvm::SymbolTableList<llvm::Function> &GetGlobalFunctions() const;

  /// Create visual representation.
  std::string ToString() const;

private:
  // Literals.
  void Visit(const frontEnd::ASTBooleanLiteral *) override;
  void Visit(const frontEnd::ASTIntegerLiteral *) override;
  void Visit(const frontEnd::ASTFloatingPointLiteral *) override;
  void Visit(const frontEnd::ASTStringLiteral *) override;

  // Operators.
  void Visit(const frontEnd::ASTBinaryOperator *) override;
  void Visit(const frontEnd::ASTUnaryOperator *) override;

  // Inside-loop statements.
  void Visit(const frontEnd::ASTBreakStmt *) override {}
  void Visit(const frontEnd::ASTContinueStmt *) override {}

  // Loop statements.
  void Visit(const frontEnd::ASTForStmt *) override;
  void Visit(const frontEnd::ASTWhileStmt *) override;
  void Visit(const frontEnd::ASTDoWhileStmt *) override;

  // Condition statements.
  void Visit(const frontEnd::ASTIfStmt *) override;

  // Function statements.
  void Visit(const frontEnd::ASTFunctionDecl *) override;
  void Visit(const frontEnd::ASTFunctionCall *) override;
  void Visit(const frontEnd::ASTFunctionPrototype *) override;

  // Declarations.
  void Visit(const frontEnd::ASTArrayDecl *) override {
#warning "Code gen for array decl is not implemented"
  }

  void Visit(const frontEnd::ASTVarDecl *) override;

  // The rest.
  void Visit(const frontEnd::ASTSymbol *) override;
  void Visit(const frontEnd::ASTCompoundStmt *) override;
  void Visit(const frontEnd::ASTReturnStmt *) override;

  /// Anayzed root AST node.
  frontEnd::ASTNode *Root;
  /// Variables pool.
  DeclsStorage DeclStorage;
  /// Consequence of using visitor pattern. since we cannot return anything from
  /// visit functions.
  llvm::Value *LastInstr;
  /// LLVM stuff.
  llvm::LLVMContext IRCtx;
  /// LLVM stuff.
  llvm::Module IRModule;
  /// LLVM stuff.
  llvm::IRBuilder<> IRBuilder;
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_CODEGEN_HPP