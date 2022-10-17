/* ASTVisitor.hpp - Common-use class to traverse the AST.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_HPP

#include "FrontEnd/AST/ASTFwdDecl.hpp"

namespace weak {

class ASTVisitor {
public:
  virtual ~ASTVisitor() noexcept = default;

  virtual void Visit(const ASTArrayDecl *) = 0;
  virtual void Visit(const ASTArrayAccess *) = 0;
  virtual void Visit(const ASTBinaryOperator *) = 0;
  virtual void Visit(const ASTBooleanLiteral *) = 0;
  virtual void Visit(const ASTBreakStmt *) = 0;
  virtual void Visit(const ASTCharLiteral *) = 0;
  virtual void Visit(const ASTCompoundStmt *) = 0;
  virtual void Visit(const ASTContinueStmt *) = 0;
  virtual void Visit(const ASTDoWhileStmt *) = 0;
  virtual void Visit(const ASTFloatingPointLiteral *) = 0;
  virtual void Visit(const ASTForStmt *) = 0;
  virtual void Visit(const ASTFunctionDecl *) = 0;
  virtual void Visit(const ASTFunctionCall *) = 0;
  virtual void Visit(const ASTFunctionPrototype *) = 0;
  virtual void Visit(const ASTIfStmt *) = 0;
  virtual void Visit(const ASTIntegerLiteral *) = 0;
  virtual void Visit(const ASTReturnStmt *) = 0;
  virtual void Visit(const ASTStringLiteral *) = 0;
  virtual void Visit(const ASTSymbol *) = 0;
  virtual void Visit(const ASTUnaryOperator *) = 0;
  virtual void Visit(const ASTVarDecl *) = 0;
  virtual void Visit(const ASTWhileStmt *) = 0;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_HPP