/* CodeGen.hpp - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_MIDDLE_END_CODEGEN_HPP
#define WEAK_COMPILER_MIDDLE_END_CODEGEN_HPP

#include "FrontEnd/AST/ASTVisitor.hpp"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include <map>

namespace weak {
namespace frontEnd {

class ASTNode;
class ASTBinaryOperator;
class ASTBooleanLiteral;
class ASTBreakStmt;
class ASTCompoundStmt;
class ASTContinueStmt;
class ASTDoWhileStmt;
class ASTFloatingPointLiteral;
class ASTForStmt;
class ASTFunctionDecl;
class ASTFunctionCall;
class ASTFunctionPrototype;
class ASTIfStmt;
class ASTIntegerLiteral;
class ASTReturnStmt;
class ASTStringLiteral;
class ASTSymbol;
class ASTUnaryOperator;
class ASTVarDecl;
class ASTWhileStmt;

} // namespace frontEnd
} // namespace weak

namespace weak {
namespace middleEnd {

class CodeGen : private frontEnd::ASTVisitor {
public:
  CodeGen(frontEnd::ASTNode *TheRoot);

  /// \todo: Move object file formation somewhere else.
  void CreateCode(std::string_view ObjectFilePath);

  std::string ToString();

private:
  // Literals.
  virtual void Visit(const frontEnd::ASTBooleanLiteral *) const override;
  virtual void Visit(const frontEnd::ASTIntegerLiteral *) const override;
  virtual void Visit(const frontEnd::ASTFloatingPointLiteral *) const override;
  virtual void Visit(const frontEnd::ASTStringLiteral *) const override;

  // Operators.
  virtual void Visit(const frontEnd::ASTBinaryOperator *) const override;
  virtual void Visit(const frontEnd::ASTUnaryOperator *) const override;

  // Inside-loop statements.
  virtual void Visit(const frontEnd::ASTBreakStmt *) const override {}
  virtual void Visit(const frontEnd::ASTContinueStmt *) const override {}

  // Loop statements.
  virtual void Visit(const frontEnd::ASTForStmt *) const override;
  virtual void Visit(const frontEnd::ASTWhileStmt *) const override;
  virtual void Visit(const frontEnd::ASTDoWhileStmt *) const override;

  // Condition statements.
  virtual void Visit(const frontEnd::ASTIfStmt *) const override;

  // Function statements.
  virtual void Visit(const frontEnd::ASTFunctionDecl *) const override;
  virtual void Visit(const frontEnd::ASTFunctionCall *) const override;
  virtual void Visit(const frontEnd::ASTFunctionPrototype *) const override;

  // The rest.
  virtual void Visit(const frontEnd::ASTSymbol *) const override;
  virtual void Visit(const frontEnd::ASTCompoundStmt *) const override;
  virtual void Visit(const frontEnd::ASTReturnStmt *) const override;
  virtual void Visit(const frontEnd::ASTVarDecl *) const override;

  frontEnd::ASTNode *Root;
  mutable llvm::Value *LastEmitted;
  mutable llvm::LLVMContext LLVMCtx;
  mutable llvm::Module LLVMModule;
  mutable llvm::IRBuilder<> CodeBuilder;
  mutable std::map<std::string, llvm::AllocaInst *> VariablesMapping;
  mutable bool IsReturnValue;
};

} // namespace middleEnd
} // namespace weak

#endif // WEAK_COMPILER_MIDDLE_END_CODEGEN_HPP