/* ASTFunctionDecl.hpp - AST node to represent a function itself.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_HPP

#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <string>
#include <vector>

namespace weak {

class ASTFunctionDecl : public ASTNode {
public:
  ASTFunctionDecl(TokenType TheReturnType, std::string &&TheName,
                  std::vector<ASTNode *> &&TheArguments,
                  ASTCompoundStmt *TheBody, unsigned TheLineNo = 0U,
                  unsigned TheColumnNo = 0U);

  ~ASTFunctionDecl();

  void Accept(ASTVisitor *) override;

  TokenType GetReturnType() const;
  const std::string &GetName() const;
  std::vector<ASTNode *> &&GetArguments();
  const std::vector<ASTNode *> &GetArguments() const;
  ASTCompoundStmt *GetBody() const;

private:
  TokenType ReturnType;
  std::string Name;
  std::vector<ASTNode *> Arguments;
  ASTCompoundStmt *Body;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_HPP