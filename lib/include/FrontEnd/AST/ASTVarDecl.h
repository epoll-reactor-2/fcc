/* ASTVarDecl.h - AST node to represent a variable declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/DataType.h"
#include <string>

namespace weak {

class ASTVarDecl : public ASTNode {
public:
  ASTVarDecl(
    weak::DataType  DT,
    std::string     Name,
    ASTNode        *Body,
    unsigned        LineNo,
    unsigned        ColumnNo
  );

  ASTVarDecl(
    weak::DataType  DT,
    std::string     TypeName,
    std::string     Name,
    ASTNode        *Body,
    unsigned        LineNo,
    unsigned        ColumnNo
  );

  ~ASTVarDecl();

  void Accept(ASTVisitor *) override;

  weak::DataType DataType() const;
  const std::string &Name() const;
  const std::string &TypeName() const;
  ASTNode *Body() const;

private:
  weak::DataType mDataType;
  std::string mTypeName;
  std::string mName;
  ASTNode *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H