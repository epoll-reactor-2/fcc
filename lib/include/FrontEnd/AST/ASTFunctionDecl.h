/* ASTFunctionDecl.h - AST node to represent a function itself.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H

#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/Token.h"
#include <string>
#include <vector>

namespace weak {

class ASTFunctionDecl : public ASTNode {
public:
  ASTFunctionDecl(TokenType ReturnType, std::string &&Name,
                  std::vector<ASTNode *> &&Arguments, ASTCompound *Body,
                  unsigned LineNo, unsigned ColumnNo);

  ~ASTFunctionDecl();

  void Accept(ASTVisitor *) override;

  TokenType ReturnType() const;
  const std::string &Name() const;
  const std::vector<ASTNode *> &Arguments() const;
  ASTCompound *Body() const;

private:
  TokenType mReturnType;
  std::string mName;
  std::vector<ASTNode *> mArguments;
  ASTCompound *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H