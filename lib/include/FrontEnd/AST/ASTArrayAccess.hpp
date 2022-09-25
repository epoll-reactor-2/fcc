/* ASTArrayAccess.hpp - AST node to represent array access operator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <memory>

namespace weak {
namespace frontEnd {

class ASTArrayAccess : public ASTNode {
public:
  ASTArrayAccess(std::string TheSymbolName, std::unique_ptr<ASTNode> &&TheIndex,
                 unsigned TheLineNo, unsigned TheColumnNo);

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  const std::string &GetSymbolName() const;
  const std::unique_ptr<ASTNode> &GetIndex() const;

private:
  std::string SymbolName;
  std::unique_ptr<ASTNode> Index;
};

} // namespace frontEnd
} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_ACCESS_HPP