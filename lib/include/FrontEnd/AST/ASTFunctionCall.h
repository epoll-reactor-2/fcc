/* ASTFunctionCall.h - AST node to represent a function call statement.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_CALL_H
#define WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_CALL_H

#include "FrontEnd/AST/ASTNode.h"
#include <string>
#include <vector>

namespace weak {

class ASTFunctionCall : public ASTNode {
public:
  ASTFunctionCall(std::string &&Name, std::vector<ASTNode *> &&Arguments,
                  unsigned LineNo, unsigned ColumnNo);

  ~ASTFunctionCall();

  void Accept(ASTVisitor *) override;

  const std::string &Name() const;
  const std::vector<ASTNode *> &Arguments() const;

private:
  std::string mName;
  std::vector<ASTNode *> mArguments;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_AST_AST_FUNCTION_CALL_H