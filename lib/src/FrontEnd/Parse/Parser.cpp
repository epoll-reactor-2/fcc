/* Parser.cpp - Implementation of syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/AST/ASTArrayAccess.h"
#include "FrontEnd/AST/ASTArrayDecl.h"
#include "FrontEnd/AST/ASTBinaryOperator.h"
#include "FrontEnd/AST/ASTBooleanLiteral.h"
#include "FrontEnd/AST/ASTBreakStmt.h"
#include "FrontEnd/AST/ASTCharLiteral.h"
#include "FrontEnd/AST/ASTCompoundStmt.h"
#include "FrontEnd/AST/ASTContinueStmt.h"
#include "FrontEnd/AST/ASTDoWhileStmt.h"
#include "FrontEnd/AST/ASTFloatingPointLiteral.h"
#include "FrontEnd/AST/ASTForStmt.h"
#include "FrontEnd/AST/ASTFunctionCall.h"
#include "FrontEnd/AST/ASTFunctionDecl.h"
#include "FrontEnd/AST/ASTFunctionPrototype.h"
#include "FrontEnd/AST/ASTIfStmt.h"
#include "FrontEnd/AST/ASTIntegerLiteral.h"
#include "FrontEnd/AST/ASTNode.h"
#include "FrontEnd/AST/ASTReturnStmt.h"
#include "FrontEnd/AST/ASTStringLiteral.h"
#include "FrontEnd/AST/ASTStructDecl.h"
#include "FrontEnd/AST/ASTSymbol.h"
#include "FrontEnd/AST/ASTUnaryOperator.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/AST/ASTWhileStmt.h"
#include "Utility/Diagnostic.h"
#include <cassert>

namespace weak {

Parser::Parser(const Token *TheBufStart, const Token *TheBufEnd)
    : BufStart(TheBufStart), BufEnd(TheBufEnd), TokenPtr(BufStart),
      LoopsDepth(0U) {
  assert(BufStart);
  assert(BufEnd);
  assert(BufStart <= BufEnd);
}

std::unique_ptr<ASTCompoundStmt> Parser::Parse() {
  std::vector<ASTNode *> Stmts;
  while (TokenPtr != BufEnd) {
    switch (const Token &T = PeekCurrent(); T.Type) {
    case TOK_STRUCT:
      Stmts.push_back(ParseStructDecl());
      break;
    case TOK_VOID:
    case TOK_INT:
    case TOK_CHAR:
    case TOK_STRING:
    case TOK_FLOAT:
    case TOK_BOOLEAN: // Fall through.
      Stmts.push_back(ParseFunctionDecl());
      break;
    default:
      weak::CompileError(T.LineNo, T.ColumnNo)
          << "Functions as global statements supported only";
      break;
    }
  }
  return std::unique_ptr<ASTCompoundStmt>(
      new ASTCompoundStmt(std::move(Stmts)));
}

ASTNode *Parser::ParseFunctionDecl() {
  /// Guaranteed data type, no checks needed.
  const Token &ReturnType = ParseReturnType();
  const Token &FunctionName = PeekNext();
  std::vector<ASTNode *> ParameterList;

  if (FunctionName.Type != TOK_SYMBOL)
    weak::CompileError(FunctionName.LineNo, FunctionName.ColumnNo)
        << "Function name expected";

  Require('(');
  ParameterList = ParseParameterList();
  Require(')');

  if (PeekCurrent().Is('{')) {
    auto *Block = ParseBlock();

    return new ASTFunctionDecl(ReturnType.Type, std::string(FunctionName.Data),
                               std::move(ParameterList), Block,
                               ReturnType.LineNo, ReturnType.ColumnNo);
  }

  Require(';');
  return new ASTFunctionPrototype(
      ReturnType.Type, std::string(FunctionName.Data), std::move(ParameterList),
      ReturnType.LineNo, ReturnType.ColumnNo);
}

ASTNode *Parser::ParseFunctionCall() {
  const Token &FunctionName = PeekNext();
  std::string Name = FunctionName.Data;
  std::vector<ASTNode *> Arguments;

  Require('(');

  auto Finish = [&] {
    return new ASTFunctionCall(std::move(Name), std::move(Arguments),
                               FunctionName.LineNo, FunctionName.ColumnNo);
  };

  if (PeekNext().Is(')'))
    return Finish();

  --TokenPtr;
  while (!PeekCurrent().Is(')')) {
    Arguments.push_back(ParseLogicalOr());
    if (Require({')', ','}).Is(')'))
      /// Move back to token before '(' and break on next iteration.
      --TokenPtr;
  }

  Require(')');

  return Finish();
}

ASTNode *Parser::ParseVarDeclWithoutInitializer() {
  const Token &DataType = ParseType();
  const Token &VariableName = PeekNext();

  if (VariableName.Type != TOK_SYMBOL)
    weak::CompileError(VariableName.LineNo, VariableName.ColumnNo)
        << "Variable name expected";

  return new ASTVarDecl(DataType.Type, std::string(VariableName.Data),
                        /*DeclareBody=*/nullptr, DataType.LineNo,
                        DataType.ColumnNo);
}

ASTNode *Parser::ParseArrayDecl() {
  const Token &DataType = ParseType();
  std::string VariableName = PeekNext().Data;
  const Token &T = PeekNext();

  std::vector<unsigned> ArityList;

  --TokenPtr;

  do {
    Require('[');

    auto *Constant = ParseConstant();

    if (!Constant->Is(AST_INTEGER_LITERAL))
      weak::CompileError(T.LineNo, T.ColumnNo)
          << "Integer size declarator expected";

    const auto *ArraySize = static_cast<const ASTIntegerLiteral *>(Constant);

    ArityList.push_back(ArraySize->GetValue());

    /// We need only number, not whole AST node, so we can
    /// get rid of it.
    delete ArraySize;

    Require(']');
  } while (!PeekCurrent().Is(',') && /// Function parameter.
           !PeekCurrent().Is(')') && /// Last function parameter.
           !PeekCurrent().Is(';'));  /// End of declaration.

  return new ASTArrayDecl(DataType.Type, std::move(VariableName),
                          std::move(ArityList), DataType.LineNo,
                          DataType.ColumnNo);
}

ASTNode *Parser::ParseVarDecl() {
  const Token &DataType = ParseType();
  std::string VariableName = PeekNext().Data;
  const Token &T = PeekNext();

  if (T.Is('='))
    return new ASTVarDecl(DataType.Type, std::move(VariableName),
                          ParseLogicalOr(), DataType.LineNo, DataType.ColumnNo);

  /// This is placed here because language supports nested functions.
  if (T.Is('(')) {
    --TokenPtr; /// Open paren.
    --TokenPtr; /// Function name.
    --TokenPtr; /// Data type.
    return ParseFunctionDecl();
  }

  if (T.Is('[')) {
    --TokenPtr; /// Open paren.
    --TokenPtr; /// Declaration name.
    --TokenPtr; /// Data type.
    return ParseArrayDecl();
  }

  weak::CompileError(T.LineNo, T.ColumnNo)
      << "Expected function, variable or array declaration";
  weak::UnreachablePoint();
}

ASTNode *Parser::ParseDecl() {
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_STRUCT:
    return ParseStructDecl();
  case TOK_VOID:
  case TOK_INT:
  case TOK_CHAR:
  case TOK_STRING:
  case TOK_FLOAT:
  case TOK_BOOLEAN: // Fall through.
    return ParseDeclWithoutInitializer();
  default:
    weak::CompileError(T.LineNo, T.ColumnNo) << "Declaration expected";
    weak::UnreachablePoint();
  }
}

ASTNode *Parser::ParseStructDecl() {
  std::vector<ASTNode *> Decls;

  const Token &Start = Require(TOK_STRUCT);
  const Token &Name = Require(TOK_SYMBOL);

  Require('{');

  while (!PeekCurrent().Is('}')) {
    Decls.push_back(ParseDecl());
    Require(';');
  }

  Require('}');

  return new ASTStructDecl(Name.Data, std::move(Decls), Start.LineNo,
                           Start.ColumnNo);
}

const Token &Parser::ParseType() {
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_INT:
  case TOK_FLOAT:
  case TOK_CHAR:
  case TOK_STRING:
  case TOK_BOOLEAN: // Fall through.
    PeekNext();
    return T;
  default:
    weak::CompileError(T.LineNo, T.ColumnNo)
        << "Data type expected, got " << TokenToString(T.Type);
    weak::UnreachablePoint();
  }
}

const Token &Parser::ParseReturnType() {
  const Token &T = PeekCurrent();
  if (T.Type != TOK_VOID)
    return ParseType();
  PeekNext();
  return T;
}

ASTNode *Parser::ParseDeclWithoutInitializer() {
  unsigned Offset = 0U;
  ++Offset; /// Data type.
  ++Offset; /// Parameter name.
  if ((TokenPtr + Offset)->Is('['))
    return ParseArrayDecl();

  return ParseVarDeclWithoutInitializer();
}

std::vector<ASTNode *> Parser::ParseParameterList() {
  std::vector<ASTNode *> List;
  if (PeekNext().Is(')')) {
    --TokenPtr;
    return List;
  }

  --TokenPtr;
  while (!PeekCurrent().Is(')')) {
    List.push_back(ParseDeclWithoutInitializer());
    if (Require({')', ','}).Is(')')) {
      /// Move back to token before '('.
      --TokenPtr;
      break;
    }
  }
  return List;
}

ASTCompoundStmt *Parser::ParseBlock() {
  if (LoopsDepth > 0)
    return ParseIterationBlock();

  std::vector<ASTNode *> Stmts;
  const Token &Start = Require('{');

  while (!PeekCurrent().Is('}')) {
    Stmts.push_back(ParseStmt());
    switch (ASTType Type = Stmts.back()->GetASTType(); Type) {
    case AST_BINARY:
    case AST_POSTFIX_UNARY:
    case AST_PREFIX_UNARY:
    case AST_SYMBOL:
    case AST_RETURN_STMT:
    case AST_DO_WHILE_STMT:
    case AST_VAR_DECL:
    case AST_ARRAY_DECL:
    case AST_ARRAY_ACCESS:
    case AST_FUNCTION_CALL: // Fall through.
      Require(';');
      break;
    default:
      break;
    }
  }
  Require('}');

  return new ASTCompoundStmt(std::move(Stmts), Start.LineNo, Start.ColumnNo);
}

ASTCompoundStmt *Parser::ParseIterationBlock() {
  std::vector<ASTNode *> Stmts;
  const Token &Start = Require('{');

  while (!PeekCurrent().Is('}')) {
    Stmts.push_back(ParseLoopStmt());
    switch (ASTType Type = Stmts.back()->GetASTType(); Type) {
    case AST_BINARY:
    case AST_POSTFIX_UNARY:
    case AST_PREFIX_UNARY:
    case AST_SYMBOL:
    case AST_RETURN_STMT:
    case AST_BREAK_STMT:
    case AST_CONTINUE_STMT:
    case AST_DO_WHILE_STMT:
    case AST_VAR_DECL:
    case AST_FUNCTION_CALL: // Fall through.
      Require(';');
      break;
    default:
      break;
    }
  }
  Require('}');

  return new ASTCompoundStmt(std::move(Stmts), Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseStmt() {
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_IF:
    return ParseSelectionStmt();
  case TOK_FOR:
  case TOK_DO:
  case TOK_WHILE: // Fall through.
    return ParseIterationStmt();
  case TOK_RETURN:
    return ParseJumpStmt();
  case TOK_INT:
  case TOK_CHAR:
  case TOK_FLOAT:
  case TOK_STRING:
  case TOK_BOOLEAN:
  case TOK_SYMBOL: // Fall through.
    return ParseExpr();
  case TOK_INC:
  case TOK_DEC: // Fall through.
    return ParsePrefixUnary();
  default:
    weak::CompileError(T.LineNo, T.ColumnNo)
        << "Unexpected token: " << TokenToString(T.Type);
    weak::UnreachablePoint();
  }
}

ASTNode *Parser::ParseSelectionStmt() {
  ASTNode *Condition{nullptr};
  ASTCompoundStmt *ThenBody{nullptr};
  ASTCompoundStmt *ElseBody{nullptr};
  const Token &Start = Require(TOK_IF);

  Require('(');
  Condition = ParseLogicalOr();
  Require(')');
  ThenBody = ParseBlock();

  if (Match(TOK_ELSE))
    ElseBody = ParseBlock();

  return new ASTIfStmt(Condition, ThenBody, ElseBody, Start.LineNo,
                       Start.ColumnNo);
}

ASTNode *Parser::ParseIterationStmt() {
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_FOR:
    return ParseForStmt();
  case TOK_DO:
    return ParseDoWhileStmt();
  case TOK_WHILE:
    return ParseWhileStmt();
  default:
    weak::UnreachablePoint("Should not reach here");
  }
}

ASTNode *Parser::ParseForStmt() {
  const Token &Start = Require(TOK_FOR);
  Require('(');

  ASTNode *Init{nullptr};
  if (!PeekNext().Is(';')) {
    --TokenPtr;
    Init = ParseExpr();
    PeekNext();
  }

  ASTNode *Condition{nullptr};
  if (!PeekNext().Is(';')) {
    --TokenPtr;
    Condition = ParseExpr();
    PeekNext();
  }

  ASTNode *Increment{nullptr};
  if (!PeekNext().Is(';')) {
    --TokenPtr;
    Increment = ParseExpr();
    PeekNext();
  }
  --TokenPtr;

  ++LoopsDepth;

  Require(')');
  auto *Body = ParseIterationBlock();

  --LoopsDepth;

  return new ASTForStmt(Init, Condition, Increment, Body, Start.LineNo,
                        Start.ColumnNo);
}

ASTNode *Parser::ParseDoWhileStmt() {
  const Token &Start = Require(TOK_DO);

  ++LoopsDepth;

  auto *Body = ParseIterationBlock();

  --LoopsDepth;

  Require(TOK_WHILE);

  Require('(');
  auto *Condition = ParseLogicalOr();
  Require(')');

  return new ASTDoWhileStmt(Body, Condition, Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseWhileStmt() {
  const Token &Start = Require(TOK_WHILE);
  Require('(');
  auto *Condition = ParseLogicalOr();
  Require(')');

  ++LoopsDepth;

  auto *Body = ParseIterationBlock();

  --LoopsDepth;

  return new ASTWhileStmt(Condition, Body, Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseLoopStmt() {
  switch (const Token &T = PeekNext(); T.Type) {
  case TOK_BREAK:
    return new ASTBreakStmt(T.LineNo, T.ColumnNo);
  case TOK_CONTINUE:
    return new ASTContinueStmt(T.LineNo, T.ColumnNo);
  default:
    --TokenPtr;
    return ParseStmt();
  }
}

ASTNode *Parser::ParseJumpStmt() {
  const Token &Start = Require(TOK_RETURN);
  ASTNode *Body{nullptr};
  if (!Match(';')) {
    /// This is `return;` case.
    /// Rollback to allow match ';' in block parse function.
    Body = ParseExpr();
  } else
    /// Go back to body of return statement.
    --TokenPtr;
  /// We want to forbid expressions like int var = var = var, so we
  /// expect the first expression to have the precedence is lower than
  /// the assignment operator.
  return new ASTReturnStmt(Body, Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseArrayAccess() {
  const Token &Symbol = PeekNext();

  Require('[');
  auto *Expr = ParseExpr();
  Require(']');

  return new ASTArrayAccess(Symbol.Data, Expr, Symbol.LineNo, Symbol.ColumnNo);
}

ASTNode *Parser::ParseExpr() {
  switch (PeekCurrent().Type) {
  case TOK_INT:
  case TOK_CHAR:
  case TOK_FLOAT:
  case TOK_STRING:
  case TOK_BOOLEAN: // Fall through.
    return ParseVarDecl();
  default:
    return ParseAssignment();
  }
}

ASTNode *Parser::ParseAssignment() {
  auto *Expr = ParseLogicalOr();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_ASSIGN:
    case TOK_MUL_ASSIGN:
    case TOK_DIV_ASSIGN:
    case TOK_MOD_ASSIGN:
    case TOK_PLUS_ASSIGN:
    case TOK_MINUS_ASSIGN:
    case TOK_SHL_ASSIGN:
    case TOK_SHR_ASSIGN:
    case TOK_BIT_AND_ASSIGN:
    case TOK_BIT_OR_ASSIGN:
    case TOK_XOR_ASSIGN: // Fall through.
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseAssignment(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseLogicalOr() {
  auto *Expr = ParseLogicalAnd();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_OR:
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseLogicalOr(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseLogicalAnd() {
  auto *Expr = ParseInclusiveOr();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_AND:
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseLogicalAnd(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseInclusiveOr() {
  auto *Expr = ParseExclusiveOr();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_BIT_OR:
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseInclusiveOr(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseExclusiveOr() {
  auto *Expr = ParseAnd();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_XOR:
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseExclusiveOr(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseAnd() {
  auto *Expr = ParseEquality();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_BIT_AND:
      Expr =
          new ASTBinaryOperator(T.Type, Expr, ParseAnd(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseEquality() {
  auto *Expr = ParseRelational();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_EQ:
    case TOK_NEQ: // Fall through.
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseEquality(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseRelational() {
  auto *Expr = ParseShift();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_GT:
    case TOK_LT:
    case TOK_GE:
    case TOK_LE: // Fall through.
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseRelational(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseShift() {
  auto *Expr = ParseAdditive();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_SHL:
    case TOK_SHR: // Fall through.
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseShift(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseAdditive() {
  auto *Expr = ParseMultiplicative();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_PLUS:
    case TOK_MINUS: // Fall through.
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseAdditive(), T.LineNo,
                                   T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseMultiplicative() {
  auto *Expr = ParsePrefixUnary();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_STAR:
    case TOK_SLASH:
    case TOK_MOD: // Fall through.
      Expr = new ASTBinaryOperator(T.Type, Expr, ParseMultiplicative(),
                                   T.LineNo, T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParsePrefixUnary() {
  switch (const Token &T = PeekNext(); T.Type) {
  case TOK_INC:
  case TOK_DEC: // Fall through.
    return new ASTUnaryOperator(ASTUnaryOperator::PREFIX, T.Type,
                                ParsePostfixUnary(), T.LineNo, T.ColumnNo);
  default:
    /// Rollback current token pointer because there's no unary operator.
    --TokenPtr;
    return ParsePostfixUnary();
  }
}

ASTNode *Parser::ParsePostfixUnary() {
  auto *Expr = ParsePrimary();
  while (true) {
    switch (const Token &T = PeekNext(); T.Type) {
    case TOK_INC:
    case TOK_DEC: // Fall through.
      Expr = new ASTUnaryOperator(ASTUnaryOperator::POSTFIX, T.Type, Expr,
                                  T.LineNo, T.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseSymbol() {
  const Token &Start = *(TokenPtr - 1);
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_OPEN_PAREN: {
    --TokenPtr;
    return ParseFunctionCall();
  }
  case TOK_OPEN_BOX_BRACKET: {
    --TokenPtr;
    return ParseArrayAccess();
  }
  default:
    return new ASTSymbol(Start.Data, Start.LineNo, Start.ColumnNo);
  }
}

ASTNode *Parser::ParsePrimary() {
  switch (const Token &T = PeekNext(); T.Type) {
  case TOK_SYMBOL:
    return ParseSymbol();
  case TOK_OPEN_PAREN: {
    /// We expect all binary/unary/constant statements expect assignment.
    auto *Expr = ParseLogicalOr();
    Require(')');
    return Expr;
  }
  default:
    --TokenPtr;
    return ParseConstant();
  }
}

ASTNode *Parser::ParseConstant() {
  switch (const Token &T = PeekNext(); T.Type) {
  case TOK_INTEGRAL_LITERAL:
    return new ASTIntegerLiteral(std::stoi(T.Data), T.LineNo, T.ColumnNo);

  case TOK_FLOATING_POINT_LITERAL:
    return new ASTFloatingPointLiteral(std::stof(T.Data), T.LineNo, T.ColumnNo);

  case TOK_STRING_LITERAL:
    return new ASTStringLiteral(T.Data, T.LineNo, T.ColumnNo);

  case TOK_CHAR_LITERAL:
    return new ASTCharLiteral(T.Data[0], T.LineNo, T.ColumnNo);

  case TOK_FALSE:
  case TOK_TRUE:
    return new ASTBooleanLiteral(T.Type == TOK_TRUE, T.LineNo, T.ColumnNo);

  default:
    weak::CompileError(T.LineNo, T.ColumnNo)
        << "Literal expected, got " << TokenToString(T.Type);
    weak::UnreachablePoint();
  }
}

const Token &Parser::PeekNext() {
  AssertNotBufEnd();
  return *TokenPtr++;
}

const Token &Parser::PeekCurrent() const {
  AssertNotBufEnd();
  return *TokenPtr;
}

bool Parser::Match(const std::vector<TokenType> &Expected) {
  AssertNotBufEnd();
  for (TokenType Token : Expected) {
    if (TokenPtr == BufEnd)
      return false;
    if (PeekCurrent().Type == Token) {
      PeekNext();
      return true;
    }
  }
  return false;
}

bool Parser::Match(TokenType Expected) {
  return Match(std::vector<TokenType>{Expected});
}

bool Parser::Match(const std::vector<char> &Expected) {
  std::vector<TokenType> Tokens;
  for (char E : Expected)
    Tokens.push_back(CharToToken(E));
  return Match(Tokens);
}

bool Parser::Match(char Expected) { return Match(CharToToken(Expected)); }

static std::string TokensToString(const std::vector<TokenType> &Tokens) {
  std::string Result;

  for (const auto &T : Tokens) {
    Result += TokenToString(T);
    Result += ", ";
  }

  if (!Result.empty()) {
    Result.pop_back();
    Result.pop_back();
  }

  return Result;
}

const Token &Parser::Require(const std::vector<TokenType> &Expected) {
  AssertNotBufEnd();
  if (Match(Expected))
    /// Something from vector successfully matched and located in previous
    /// token.
    return *(TokenPtr - 1);

  weak::CompileError(TokenPtr->LineNo, TokenPtr->ColumnNo)
      << "Expected " << TokensToString(Expected) << ", got "
      << TokenToString(TokenPtr->Type);
  weak::UnreachablePoint();
}

const Token &Parser::Require(TokenType Expected) {
  return Require(std::vector<TokenType>{Expected});
}

const Token &Parser::Require(const std::vector<char> &Expected) {
  std::vector<TokenType> Tokens;
  for (char E : Expected)
    Tokens.push_back(CharToToken(E));
  return Require(Tokens);
}

const Token &Parser::Require(char Expected) {
  return Require(std::vector<char>{Expected});
}

void Parser::AssertNotBufEnd() const {
  if (TokenPtr == BufEnd)
    weak::CompileError(TokenPtr->LineNo, TokenPtr->LineNo)
        << "End of buffer reached";
}

} // namespace weak