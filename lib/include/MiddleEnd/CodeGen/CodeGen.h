/* CodeGen.h - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_CODEGEN_H
#define WEAK_COMPILER_MIDDLE_END_CODEGEN_H

#include "FrontEnd/AST/ASTVisitor.h"
#include "MiddleEnd/Storage/DeclsStorage.h"
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

  llvm::Module &Module();

  /// Get list of already created global variables.
  const llvm::SymbolTableList<llvm::GlobalVariable> &GlobalVariables() const;

  /// Get list of already created functions.
  const llvm::SymbolTableList<llvm::Function> &GlobalFunctions() const;

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
  ASTNode *mRoot;
  /// Variables pool.
  DeclsStorage mStorage;
  /// Consequence of using visitor pattern, since we cannot return anything from
  /// visit functions.
  llvm::Value *mLastInstr;
  /// LLVM stuff.
  llvm::LLVMContext mIRCtx;
  /// LLVM stuff.
  llvm::Module mIRModule;
  /// LLVM stuff.
  llvm::IRBuilder<> mIRBuilder;
};

} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_CODEGEN_H