/* ASTFunctionDecl.h - AST node to represent a function itself.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H

#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/Lex/DataType.h"
#include <string>
#include <vector>

namespace weak {

class ASTCompound;

class ASTFunctionDecl : public ASTNode {
public:
  ASTFunctionDecl(DataType ReturnType, std::string Name,
                  std::vector<ASTNode *> Args, ASTCompound *Body,
                  unsigned LineNo, unsigned ColumnNo);

  ~ASTFunctionDecl();

  void Accept(ASTVisitor *) override;

  DataType ReturnType() const;
  const std::string &Name() const;
  const std::vector<ASTNode *> &Args() const;
  ASTCompound *Body() const;

private:
  DataType mReturnType;
  std::string mName;
  std::vector<ASTNode *> mArgs;
  ASTCompound *mBody;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_DECL_H