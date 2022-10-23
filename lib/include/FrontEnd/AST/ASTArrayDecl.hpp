/* ASTArrayDecl.hpp - AST node to represent array declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_HPP
#define WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_HPP

#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <vector>

namespace weak {

class ASTArrayDecl : public ASTNode {
public:
  ASTArrayDecl(TokenType TheDataType, std::string TheSymbolName,
               std::vector<unsigned> ArityList, unsigned TheLineNo = 0U,
               unsigned TheColumnNo = 0U);

  ASTType GetASTType() const override;
  void Accept(ASTVisitor *) override;

  TokenType GetDataType() const;
  const std::string &GetSymbolName() const;
  const std::vector<unsigned> &GetArityList() const;

private:
  /// Data type of array.
  TokenType DataType;

  /// Variable name.
  std::string SymbolName;

  /// This stores information about array arity (dimension)
  /// and size for each dimension, e.g.,
  /// for array[1][2][3], ArityList equal to { 1, 2, 3 }.
  std::vector<unsigned> ArityList;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_HPP