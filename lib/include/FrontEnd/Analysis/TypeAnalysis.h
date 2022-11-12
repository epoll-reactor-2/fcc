/* TypeAnalysis.h - Type checker.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_ANALYSIS_TYPE_ANALYSIS_H
#define WEAK_COMPILER_FRONTEND_ANALYSIS_TYPE_ANALYSIS_H

#include "FrontEnd/Analysis/ASTStorage.h"
#include "FrontEnd/Analysis/Analysis.h"
#include "FrontEnd/Lex/DataType.h"

namespace weak {

/// \brief Type checker
///
/// Performs listed below assertions.
///
/// \note Should be called after VariableUseAnalysis and FunctionAnalysis.
///
/// <table>
///   <tr>
///     <th>Expression</th>
///     <th>Semantic</th>
///   </tr>
///   <tr>
///     <th>x + y</th>
///     <td>Same operand types (int, char, float, bool).</td>
///   </tr>
///   <tr>
///     <th>++x</th>
///     <td>Int or char operand type.</td>
///   </tr>
///   <tr>
///     <th>int f() { return 1; }</th>
///     <td>Return value is of function return type.</td>
///   </tr>
///   <tr>
///     <th>int f(int) {}, f(0)</th>
///     <td>Function argument is of type in signature.</td>
///   </tr>
///   <tr>
///     <th>mem[1] | mem[var]</th>
///     <td>Integer as array index.</td>
///   </tr>
/// </table>
class TypeAnalysis : public Analysis {
public:
  TypeAnalysis(ASTNode *Root);

  void Analyze() override;

private:
  void Visit(ASTBool *) override;
  void Visit(ASTChar *) override;
  void Visit(ASTFloat *) override;
  void Visit(ASTNumber *) override;
  void Visit(ASTString *) override;

  void Visit(ASTBinary *) override;
  void Visit(ASTUnary *) override;

  void Visit(ASTArrayDecl *) override;
  void Visit(ASTVarDecl *) override;

  void Visit(ASTArrayAccess *) override;
  void Visit(ASTSymbol *) override;

  void Visit(ASTFunctionDecl *) override;
  void Visit(ASTFunctionPrototype *) override;
  void Visit(ASTFunctionCall *) override;
  void Visit(ASTReturn *) override;

  template <typename ASTFun>
  void DoCallArgumentsAnalysis(ASTNode *Decl,
                               const std::vector<ASTNode *> &Args);

  /// Analyzed root AST node.
  ASTNode *mRoot;

  ASTStorage mStorage;

  DataType mLastDataType;
  DataType mLastReturnDataType;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_ANALYSIS_TYPE_ANALYSIS_H