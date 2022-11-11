/* ASTVisitor.h - Common-use class to traverse the AST.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_H
#define WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_H

#include "FrontEnd/AST/ASTFwdDecl.h"

namespace weak {

/// Visitor for all AST statements.
///
/// By default, performs full traversal and does nothing.
class ASTVisitor {
public:
  virtual ~ASTVisitor() = default;

  virtual void Visit(ASTArrayDecl *) {}
  virtual void Visit(ASTArrayAccess *);
  virtual void Visit(ASTBinary *);
  virtual void Visit(ASTBool *) {}
  virtual void Visit(ASTBreak *) {}
  virtual void Visit(ASTChar *) {}
  virtual void Visit(ASTCompound *);
  virtual void Visit(ASTContinue *) {}
  virtual void Visit(ASTDoWhile *);
  virtual void Visit(ASTFloat *) {}
  virtual void Visit(ASTFor *);
  virtual void Visit(ASTFunctionDecl *);
  virtual void Visit(ASTFunctionCall *);
  virtual void Visit(ASTFunctionPrototype *);
  virtual void Visit(ASTIf *);
  virtual void Visit(ASTNumber *) {}
  virtual void Visit(ASTReturn *);
  virtual void Visit(ASTString *) {}
  virtual void Visit(ASTStructDecl *);
  virtual void Visit(ASTMemberAccess *);
  virtual void Visit(ASTSymbol *) {}
  virtual void Visit(ASTUnary *);
  virtual void Visit(ASTVarDecl *);
  virtual void Visit(ASTWhile *);
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VISITOR_H