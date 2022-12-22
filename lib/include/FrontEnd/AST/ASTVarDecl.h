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
    unsigned        IndirectionLvl,
    ASTNode        *Body,
    unsigned        LineNo,
    unsigned        ColumnNo
  );

  ASTVarDecl(
    weak::DataType  DT,
    std::string     TypeName,
    std::string     Name,
    unsigned        IndirectionLvl,
    ASTNode        *Body,
    unsigned        LineNo,
    unsigned        ColumnNo
  );

  ~ASTVarDecl();

  void Accept(ASTVisitor *) override;

  weak::DataType DataType() const;
  const std::string &Name() const;
  const std::string &TypeName() const;
  unsigned IndirectionLvl() const;
  ASTNode *Body() const;

private:
  /// Data type of array.
  weak::DataType mDataType;

  /// Variable name.
  std::string mName;

  /// Optional structure type name.
  std::string mTypeName;

  /// Depth of pointer, like for
  /// int ***ptr indirection level = 3, for
  /// int *ptr = 1, for
  /// int var = 0.
  unsigned mIndirectionLvl;

  ASTNode *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_VAR_DECL_H