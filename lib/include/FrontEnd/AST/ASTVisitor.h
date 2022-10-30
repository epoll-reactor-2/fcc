/* ASTVisitor.h - Common-use class to traverse the AST.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_H
#define WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_H

#include "FrontEnd/AST/ASTFwdDecl.h"

namespace weak {

class ASTVisitor {
public:
  virtual ~ASTVisitor() = default;

  virtual void Visit(const ASTArrayDecl *) = 0;
  virtual void Visit(const ASTArrayAccess *) = 0;
  virtual void Visit(const ASTBinary *) = 0;
  virtual void Visit(const ASTBool *) = 0;
  virtual void Visit(const ASTBreak *) = 0;
  virtual void Visit(const ASTChar *) = 0;
  virtual void Visit(const ASTCompound *) = 0;
  virtual void Visit(const ASTContinue *) = 0;
  virtual void Visit(const ASTDoWhile *) = 0;
  virtual void Visit(const ASTFloat *) = 0;
  virtual void Visit(const ASTFor *) = 0;
  virtual void Visit(const ASTFunctionDecl *) = 0;
  virtual void Visit(const ASTFunctionCall *) = 0;
  virtual void Visit(const ASTFunctionPrototype *) = 0;
  virtual void Visit(const ASTIf *) = 0;
  virtual void Visit(const ASTNumber *) = 0;
  virtual void Visit(const ASTReturn *) = 0;
  virtual void Visit(const ASTString *) = 0;
  virtual void Visit(const ASTStructDecl *) = 0;
  virtual void Visit(const ASTSymbol *) = 0;
  virtual void Visit(const ASTUnary *) = 0;
  virtual void Visit(const ASTVarDecl *) = 0;
  virtual void Visit(const ASTWhile *) = 0;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_H