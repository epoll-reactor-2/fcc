/* ASTArrayDecl.cpp - AST node to represent array declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTArrayDecl.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"

namespace weak {

ASTArrayDecl::ASTArrayDecl(TokenType TheDataType, std::string TheSymbolName,
                           std::vector<unsigned> TheArityList,
                           unsigned TheLineNo, unsigned TheColumnNo)
    : ASTNode(TheLineNo, TheColumnNo), DataType(TheDataType),
      SymbolName(std::move(TheSymbolName)), ArityList(std::move(TheArityList)) {
}

ASTType ASTArrayDecl::GetASTType() const { return AST_ARRAY_DECL; }

void ASTArrayDecl::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTArrayDecl::GetDataType() const { return DataType; }

const std::string &ASTArrayDecl::GetSymbolName() const { return SymbolName; }

const std::vector<unsigned> &ASTArrayDecl::GetArityList() const {
  return ArityList;
}

} // namespace weak