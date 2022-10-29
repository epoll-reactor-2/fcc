/* ASTArrayDecl.cpp - AST node to represent array declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTArrayDecl.h"
#include "FrontEnd/AST/ASTVisitor.h"

namespace weak {

ASTArrayDecl::ASTArrayDecl(TokenType DataType, std::string SymbolName,
                           std::vector<unsigned> ArityList, unsigned LineNo,
                           unsigned ColumnNo)
    : ASTNode(AST_ARRAY_DECL, LineNo, ColumnNo), mDataType(DataType),
      mSymbolName(std::move(SymbolName)), mArityList(std::move(ArityList)) {}

void ASTArrayDecl::Accept(ASTVisitor *Visitor) { Visitor->Visit(this); }

TokenType ASTArrayDecl::DataType() const { return mDataType; }

const std::string &ASTArrayDecl::SymbolName() const { return mSymbolName; }

const std::vector<unsigned> &ASTArrayDecl::ArityList() const {
  return mArityList;
}

} // namespace weak