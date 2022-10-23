/* ASTVarDecl.hpp - AST node to represent a variable declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <string>

namespace weak {

class ASTVarDecl : public ASTNode {
public:
  ASTVarDecl(TokenType TheDataType, std::string &&TheSymbolName,
             ASTNode *TheDeclBody, unsigned TheLineNo = 0U,
             unsigned TheColumnNo = 0U);

  ~ASTVarDecl();

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  TokenType GetDataType() const;
  const std::string &GetSymbolName() const;
  ASTNode *GetDeclBody() const;

private:
  TokenType DataType;
  std::string SymbolName;
  ASTNode *DeclBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_HPP