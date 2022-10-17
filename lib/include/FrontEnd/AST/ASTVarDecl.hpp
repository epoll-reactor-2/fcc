/* ASTVarDecl.hpp - AST node to represent a variable declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <memory>
#include <string>

namespace weak {

class ASTVarDecl : public ASTNode {
public:
  ASTVarDecl(TokenType TheDataType, std::string &&TheSymbolName,
             std::unique_ptr<ASTNode> &&TheDeclareBody, unsigned TheLineNo = 0U,
             unsigned TheColumnNo = 0U);

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  TokenType GetDataType() const;
  const std::string &GetSymbolName() const;
  const std::unique_ptr<ASTNode> &GetDeclareBody() const;

private:
  TokenType DataType;
  std::string SymbolName;
  std::unique_ptr<ASTNode> DeclareBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_HPP