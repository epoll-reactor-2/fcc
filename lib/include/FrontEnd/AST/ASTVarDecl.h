/* ASTVarDecl.h - AST node to represent a variable declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/Token.h"
#include <string>

namespace weak {

class ASTVarDecl : public ASTNode {
public:
  ASTVarDecl(TokenType DataType, std::string &&Name,
             ASTNode *Body, unsigned LineNo,
             unsigned ColumnNo);

  ~ASTVarDecl();

  void Accept(ASTVisitor *) override;

  TokenType DataType() const;
  const std::string &Name() const;
  ASTNode *Body() const;

private:
  TokenType mDataType;
  std::string mName;
  ASTNode *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H