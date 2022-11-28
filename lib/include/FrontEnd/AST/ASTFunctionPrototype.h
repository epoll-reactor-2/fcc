/* ASTFunctionPrototype.h - AST node to represent a function prototype.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_PROTOTYPE_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_PROTOTYPE_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/DataType.h"
#include <string>
#include <vector>

namespace weak {

class ASTFunctionPrototype : public ASTNode {
public:
  ASTFunctionPrototype(
    DataType               ReturnType,
    std::string            Name,
    std::vector<ASTNode *> Args,
    unsigned               LineNo,
    unsigned               ColumnNo
  );

  ~ASTFunctionPrototype();

  void Accept(ASTVisitor *) override;

  DataType ReturnType() const;
  const std::string &Name() const;
  const std::vector<ASTNode *> &Args() const;

private:
  DataType mReturnType;
  std::string mName;
  std::vector<ASTNode *> mArgs;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_PROTOTYPE_H