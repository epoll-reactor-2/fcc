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

  virtual void Visit(const ASTArrayDecl *) {}
  virtual void Visit(const ASTArrayAccess *) {}
  virtual void Visit(const ASTBinary *) {}
  virtual void Visit(const ASTBool *) {}
  virtual void Visit(const ASTBreak *) {}
  virtual void Visit(const ASTChar *) {}
  virtual void Visit(const ASTCompound *) {}
  virtual void Visit(const ASTContinue *) {}
  virtual void Visit(const ASTDoWhile *) {}
  virtual void Visit(const ASTFloat *) {}
  virtual void Visit(const ASTFor *) {}
  virtual void Visit(const ASTFunctionDecl *) {}
  virtual void Visit(const ASTFunctionCall *) {}
  virtual void Visit(const ASTFunctionPrototype *) {}
  virtual void Visit(const ASTIf *) {}
  virtual void Visit(const ASTNumber *) {}
  virtual void Visit(const ASTReturn *) {}
  virtual void Visit(const ASTString *) {}
  virtual void Visit(const ASTStructDecl *) {}
  virtual void Visit(const ASTSymbol *) {}
  virtual void Visit(const ASTUnary *) {}
  virtual void Visit(const ASTVarDecl *) {}
  virtual void Visit(const ASTWhile *) {}
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_H