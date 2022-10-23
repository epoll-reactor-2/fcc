/* Parser.hpp - Implementation of syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_PARSE_PARSER_HPP
#define WEAK_COMPILER_FRONTEND_PARSE_PARSER_HPP

#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <memory>
#include <vector>

namespace weak {

/// \brief LL(1) Syntax analyzer.
class Parser {
public:
  /// \note Requires random access memory layout of buffer.
  Parser(const Token *TheBufferStart, const Token *TheBufferEnd);

  /// Transform token stream to AST.
  ///
  /// \note Smart pointer is returned there to auto-cleanup
  ///       AST by calling all destructors of compound statement
  ///       down recursively. Of course, each AST node responsible
  ///       to kill it's children.
  std::unique_ptr<ASTCompoundStmt> Parse();

private:
  /// Function with or without body (prototype).
  ASTNode *ParseFunctionDecl();

  /// Function call with optional argument list.
  ASTNode *ParseFunctionCall();

  /// Expressions like `int variable`. Used in function parameters.
  ASTNode *ParseVarDeclWithoutInitializer();

  /// Array declaration of any arity, beginning from 1.
  ASTNode *ParseArrayDecl();

  /// < id > [ < expression > ].
  ASTNode *ParseArrayAccessOperator();

  /// Variable declaration with initializer.
  ASTNode *ParseVarDecl();

  /// Int, float, char, string, bool.
  const Token &ParseType();

  /// All from ParseType() or void.
  const Token &ParseReturnType();

  /// < type > < id > | < type > < id > [ < integral-literal > ].
  ASTNode *ParseParameter();

  /// ( (< type > < id > ,?)* ).
  std::vector<ASTNode *> ParseParameterList();

  /// { < iteration-stmt >* }.
  ASTCompoundStmt *ParseBlock();

  /// Block of code with break and continue statements.
  ASTCompoundStmt *ParseIterationStmtBlock();

  /// Selection, iterative, jump, assignment statement
  /// or unary/binary operator.
  ASTNode *ParseStatement();

  /// If statement.
  ASTNode *ParseSelectionStatement();

  /// For, while or do-while statement.
  ASTNode *ParseIterationStatement();

  ASTNode *ParseForStatement();

  ASTNode *ParseWhileStatement();

  ASTNode *ParseDoWhileStatement();

  /// ParseStatement, break and continue statements.
  ASTNode *ParseLoopStatement();

  /// Return statement.
  ASTNode *ParseJumpStatement();

  /// Unary/binary statement, literal, symbol, assignment, variable declaration
  /// or function call.
  ASTNode *ParseExpression();

  ASTNode *ParseAssignment();

  ASTNode *ParseLogicalOr();

  ASTNode *ParseLogicalAnd();

  ASTNode *ParseInclusiveOr();

  ASTNode *ParseExclusiveOr();

  ASTNode *ParseAnd();

  ASTNode *ParseEquality();

  ASTNode *ParseRelational();

  ASTNode *ParseShift();

  ASTNode *ParseAdditive();

  ASTNode *ParseMultiplicative();

  ASTNode *ParsePrefixUnary();

  ASTNode *ParsePostfixUnary();

  /// Symbol, function call or array access.
  ASTNode *ParseSymbolProduction();

  /// Symbol, parentheses expression or constant.
  ASTNode *ParsePrimary();

  /// Integral, floating-point, string or boolean literal.
  ASTNode *ParseConstant();

  /// Get current token from input range and move forward.
  const Token &PeekNext();

  /// Get current token from input range without moving to the next one.
  const Token &PeekCurrent() const;

  /// Return true and move current buffer pointer forward if current token
  /// matches any of expected, otherwise return false.
  bool Match(const std::vector<TokenType> &Expected);

  /// Return true and move current buffer pointer forward if current token
  /// matches given token type, otherwise return false.
  bool Match(TokenType Expected);

  /// Does the Match job, but emits compile error on mismatch.
  const Token &Require(const std::vector<TokenType> &Expected);

  /// Does the Match job, but emits compile error on mismatch.
  const Token &Require(TokenType Expected);

  /// Ensure we can move CurrentBufferPtr forward or emit compile error, if
  /// we're reached BufferEnd.
  void CheckIfHaveMoreTokens() const;

  /// First token in input stream.
  const Token *BufferStart;

  /// Pointer to after-last token in input stream, like std::end().
  const Token *BufferEnd;

  /// Current token to be processed.
  const Token *CurrentBufferPtr;

  /// Depth of currently analyzed loop. Needed for 'break', 'continue' parsing.
  std::size_t LoopsDepth;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_PARSE_PARSER_HPP