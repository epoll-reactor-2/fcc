/* ASTArrayDecl.h - AST node to represent array declaration.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/DataType.h"
#include <string>
#include <vector>

namespace weak {

class ASTArrayDecl : public ASTNode {
public:
  ASTArrayDecl(
    weak::DataType        DT,
    std::string           Name,
    std::vector<unsigned> ArityList,
    unsigned              IndirectionLvl,
    unsigned              LineNo,
    unsigned              ColumnNo
  );

  ASTArrayDecl(
    weak::DataType        DT,
    std::string           TypeName,
    std::string           Name,
    std::vector<unsigned> ArityList,
    unsigned              IndirectionLvl,
    unsigned              LineNo,
    unsigned              ColumnNo
  );

  void Accept(ASTVisitor *) override;

  weak::DataType DataType() const;
  const std::string &Name() const;
  const std::string &TypeName() const;
  const std::vector<unsigned> &ArityList() const;
  unsigned IndirectionLvl() const;

private:
  /// Data type of array.
  weak::DataType mDataType;

  /// Variable name.
  std::string mName;

  /// Optional structure type name.
  std::string mTypeName;

  /// This stores information about array arity (dimension)
  /// and size for each dimension, e.g.,
  /// for array[1][2][3], ArityList equal to { 1, 2, 3 }.
  std::vector<unsigned> mArityList;

  /// Depth of pointer, like for
  /// int ***ptr indirection level = 3, for
  /// int *ptr = 1, for
  /// int var = 0.
  unsigned mIndirectionLvl;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_H