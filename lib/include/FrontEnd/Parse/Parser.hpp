/* Parser.hpp - Implementation of syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_PARSE_PARSER_HPP
#define WEAK_COMPILER_FRONTEND_PARSE_PARSER_HPP

#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/Lex/Token.hpp"
#include <vector>

namespace weak {

/// \brief LL(1) Syntax analyzer.
class Parser {
public:
  /// \note Requires random access memory layout of buffer.
  Parser(const Token *TheBufferStart, const Token *TheBufferEnd);

  /// Transform token stream to AST.
  std::unique_ptr<ASTCompoundStmt> Parse();

private:
  /// Function with or without body (prototype).
  std::unique_ptr<ASTNode> ParseFunctionDecl();

  /// Function call with optional argument list.
  std::unique_ptr<ASTNode> ParseFunctionCall();

  /// Expressions like `int variable`. Used in function parameters.
  std::unique_ptr<ASTNode> ParseVarDeclWithoutInitializer();

  /// Array declaration of any arity, beginning from 1.
  std::unique_ptr<ASTNode> ParseArrayDecl();

  /// < id > [ < expression > ].
  std::unique_ptr<ASTNode> ParseArrayAccessOperator();

  /// Variable declaration with initializer.
  std::unique_ptr<ASTNode> ParseVarDecl();

  /// Int, float, char, string, bool.
  const Token &ParseType();

  /// All from ParseType() or void.
  const Token &ParseReturnType();

  /// < type > < id > | < type > < id > [ < integral-literal > ].
  std::unique_ptr<ASTNode> ParseParameter();

  /// ( (< type > < id > ,?)* ).
  std::vector<std::unique_ptr<ASTNode>> ParseParameterList();

  /// { < iteration-stmt >* }.
  std::unique_ptr<ASTCompoundStmt> ParseBlock();

  /// Block of code with break and continue statements.
  std::unique_ptr<ASTCompoundStmt> ParseIterationStmtBlock();

  /// Selection, iterative, jump, assignment statement
  /// or unary/binary operator.
  std::unique_ptr<ASTNode> ParseStatement();

  /// If statement.
  std::unique_ptr<ASTNode> ParseSelectionStatement();

  /// For, while or do-while statement.
  std::unique_ptr<ASTNode> ParseIterationStatement();

  std::unique_ptr<ASTNode> ParseForStatement();

  std::unique_ptr<ASTNode> ParseWhileStatement();

  std::unique_ptr<ASTNode> ParseDoWhileStatement();

  /// ParseStatement, break and continue statements.
  std::unique_ptr<ASTNode> ParseLoopStatement();

  /// Return statement.
  std::unique_ptr<ASTNode> ParseJumpStatement();

  /// Unary/binary statement, literal, symbol, assignment, variable declaration
  /// or function call.
  std::unique_ptr<ASTNode> ParseExpression();

  std::unique_ptr<ASTNode> ParseAssignment();

  std::unique_ptr<ASTNode> ParseLogicalOr();

  std::unique_ptr<ASTNode> ParseLogicalAnd();

  std::unique_ptr<ASTNode> ParseInclusiveOr();

  std::unique_ptr<ASTNode> ParseExclusiveOr();

  std::unique_ptr<ASTNode> ParseAnd();

  std::unique_ptr<ASTNode> ParseEquality();

  std::unique_ptr<ASTNode> ParseRelational();

  std::unique_ptr<ASTNode> ParseShift();

  std::unique_ptr<ASTNode> ParseAdditive();

  std::unique_ptr<ASTNode> ParseMultiplicative();

  std::unique_ptr<ASTNode> ParsePrefixUnary();

  std::unique_ptr<ASTNode> ParsePostfixUnary();

  /// Symbol, function call or array access.
  std::unique_ptr<ASTNode> ParseSymbolProduction();

  /// Symbol, parentheses expression or constant.
  std::unique_ptr<ASTNode> ParsePrimary();

  /// Integral, floating-point, string or boolean literal.
  std::unique_ptr<ASTNode> ParseConstant();

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