/* ASTFunctionPrototype.hpp - AST node to represent a function prototype.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_PROTOTYPE_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_PROTOTYPE_HPP

#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <string>
#include <vector>

namespace weak {

class ASTFunctionPrototype : public ASTNode {
public:
  ASTFunctionPrototype(TokenType TheReturnType, std::string &&TheName,
                       std::vector<ASTNode *> &&TheArguments,
                       unsigned TheLineNo = 0U, unsigned TheColumnNo = 0U);

  ~ASTFunctionPrototype();

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  TokenType GetReturnType() const;
  const std::string &GetName() const;
  std::vector<ASTNode *> &&GetArguments();
  const std::vector<ASTNode *> &GetArguments() const;

private:
  TokenType ReturnType;
  std::string Name;
  std::vector<ASTNode *> Arguments;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_PROTOTYPE_HPP