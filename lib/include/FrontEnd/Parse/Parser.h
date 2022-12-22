/* Parser.h - Implementation of syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#ifndef WEAK_COMPILER_FRONTEND_PARSE_PARSER_H
#define WEAK_COMPILER_FRONTEND_PARSE_PARSER_H

#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/Lex/DataType.h"
#include "FrontEnd/Lex/Token.h"
#include <memory>
#include <vector>

namespace weak {

/// \brief LL(1) Syntax analyzer.
class Parser {
public:
  /// \note Requires random access memory layout of buffer.
  Parser(const Token *BufStart, const Token *BufEnd);

  /// Transform token stream to AST.
  ///
  /// \note Smart pointer is returned there to auto-cleanup
  ///       AST by calling all destructors of compound statement
  ///       down recursively. Of course, each AST node responsible
  ///       to kill it's children.
  std::unique_ptr<ASTCompound> Parse();

private:
  struct LocalizedDataType {
    DataType DT;
    unsigned IndirectionLvl;
    unsigned LineNo;
    unsigned ColumnNo;
  };

  /// Function with or without body (prototype).
  ASTNode *ParseFunctionDecl();

  /// Function call with optional argument list.
  ASTNode *ParseFunctionCall();

  /// Variable declaration with initializer.
  ASTNode *ParseVarDecl();

  /// Expressions like `int variable`. Used in function parameters.
  ASTNode *ParseVarDeclWithoutInitializer();

  /// Array declaration of any arity, beginning from 1.
  ASTNode *ParseArrayDecl();

  /// < id > [ < expression > ].
  ASTNode *ParseArrayAccess();

  ASTNode *ParseDecl();

  /// User type declaration.
  ASTNode *ParseStructDecl();

  ASTNode *ParseStructVarDecl();

  /// `Structure.Field`.
  ASTNode *ParseStructFieldAccess();

  /// Int, float, char, string, bool.
  LocalizedDataType ParseType();

  /// All from ParseType() or void.
  LocalizedDataType ParseReturnType();

  /// < type > < id > | < type > < id > [ < integral-literal > ].
  ASTNode *ParseDeclWithoutInitializer();

  /// ( (< type > < id > ,?)* ).
  std::vector<ASTNode *> ParseParameterList();

  /// { < iteration-stmt >* }.
  ASTCompound *ParseBlock();

  /// Block of code with break and continue statements.
  ASTCompound *ParseIterationBlock();

  /// Selection, iterative, jump, assignment statement
  /// or unary/binary operator.
  ASTNode *ParseStmt();

  /// If statement.
  ASTNode *ParseSelectionStmt();

  /// For, while or do-while statement.
  ASTNode *ParseIterationStmt();

  ASTNode *ParseFor();

  ASTNode *ParseWhile();

  ASTNode *ParseDoWhile();

  /// ParseStmt() and break, continue.
  ASTNode *ParseLoopStmt();

  /// Return statement.
  ASTNode *ParseJumpStmt();

  /// Unary/binary statement, literal, symbol, assignment, variable declaration
  /// or function call.
  ASTNode *ParseExpr();

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
  ASTNode *ParseSymbol();

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

  /// \copydoc Match(const std::vector<TokenType> &)
  bool Match(TokenType Expected);

  /// \copydoc Match(const std::vector<TokenType> &)
  bool Match(const std::vector<char> &Expected);

  /// \copydoc Match(const std::vector<TokenType> &)
  bool Match(char Expected);

  /// Does the Match job, but emits compile error on mismatch.
  const Token &Require(const std::vector<TokenType> &Expected);

  /// \copydoc Require(const std::vector<TokenType> &)
  const Token &Require(TokenType Expected);

  /// \copydoc Require(const std::vector<TokenType> &)
  const Token &Require(const std::vector<char> &Expected);

  /// \copydoc Require(const std::vector<TokenType> &)
  const Token &Require(char Expected);

  /// Ensure we can move CurrentBufferPtr forward or emit compile error, if
  /// we're reached BufferEnd.
  void AssertNotBufEnd() const;

  /// First token in input stream.
  const Token *mBufStart;

  /// Pointer to after-last token in input stream, like std::end().
  const Token *mBufEnd;

  /// Current token to be processed.
  const Token *mTokenPtr;

  /// Depth of currently analyzed loop. Needed for 'break', 'continue' parsing.
  unsigned mLoopsDepth;
};

} // namespace weak

#endif // WEAK_COMPILER_FRONTEND_PARSE_PARSER_H
