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
    unsigned              LineNo,
    unsigned              ColumnNo
  );

  void Accept(ASTVisitor *) override;

  weak::DataType DataType() const;
  const std::string &Name() const;
  const std::vector<unsigned> &ArityList() const;

private:
  /// Data type of array.
  weak::DataType mDataType;

  /// Variable name.
  std::string mName;

  /// This stores information about array arity (dimension)
  /// and size for each dimension, e.g.,
  /// for array[1][2][3], ArityList equal to { 1, 2, 3 }.
  std::vector<unsigned> mArityList;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_ARRAY_DECL_H