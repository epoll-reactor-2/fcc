/* Parser.cpp - Implementation of syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Parse/Parser.hpp"
#include "FrontEnd/AST/ASTArrayAccess.hpp"
#include "FrontEnd/AST/ASTArrayDecl.hpp"
#include "FrontEnd/AST/ASTBinaryOperator.hpp"
#include "FrontEnd/AST/ASTBooleanLiteral.hpp"
#include "FrontEnd/AST/ASTBreakStmt.hpp"
#include "FrontEnd/AST/ASTCharLiteral.hpp"
#include "FrontEnd/AST/ASTCompoundStmt.hpp"
#include "FrontEnd/AST/ASTContinueStmt.hpp"
#include "FrontEnd/AST/ASTDoWhileStmt.hpp"
#include "FrontEnd/AST/ASTFloatingPointLiteral.hpp"
#include "FrontEnd/AST/ASTForStmt.hpp"
#include "FrontEnd/AST/ASTFunctionCall.hpp"
#include "FrontEnd/AST/ASTFunctionDecl.hpp"
#include "FrontEnd/AST/ASTFunctionPrototype.hpp"
#include "FrontEnd/AST/ASTIfStmt.hpp"
#include "FrontEnd/AST/ASTIntegerLiteral.hpp"
#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/AST/ASTReturnStmt.hpp"
#include "FrontEnd/AST/ASTStringLiteral.hpp"
#include "FrontEnd/AST/ASTStructDecl.hpp"
#include "FrontEnd/AST/ASTSymbol.hpp"
#include "FrontEnd/AST/ASTUnaryOperator.hpp"
#include "FrontEnd/AST/ASTVarDecl.hpp"
#include "FrontEnd/AST/ASTWhileStmt.hpp"
#include "Utility/Diagnostic.hpp"
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
  std::vector<ASTNode *> GlobalEntities;
  while (TokenPtr != BufEnd) {
    switch (const Token &Current = PeekCurrent(); Current.Type) {
    case TOK_STRUCT:
      GlobalEntities.push_back(ParseStructDecl());
      break;
    case TOK_VOID:
    case TOK_INT:
    case TOK_CHAR:
    case TOK_STRING:
    case TOK_FLOAT:
    case TOK_BOOLEAN: // Fall through.
      GlobalEntities.push_back(ParseFunctionDecl());
      break;
    default:
      weak::CompileError(Current.LineNo, Current.ColumnNo)
          << "Functions as global statements supported only";
      break;
    }
  }
  return std::unique_ptr<ASTCompoundStmt>(
      new ASTCompoundStmt(std::move(GlobalEntities)));
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
    const auto &T = Require({')', ','});
    if (T.Is(')'))
      // Move back to token before '(' and break on next iteration.
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
  const Token &Current = PeekNext();

  std::vector<unsigned> ArityList;

  --TokenPtr;
  while (true) {
    Require('[');

    auto *Constant = ParseConstant();

    if (Constant->GetASTType() != AST_INTEGER_LITERAL)
      weak::CompileError(Current.LineNo, Current.ColumnNo)
          << "Integer size declarator expected";

    const auto *ArraySize = static_cast<const ASTIntegerLiteral *>(Constant);

    ArityList.push_back(ArraySize->GetValue());

    /// We need only number, not whole AST node, so we can
    /// get rid of it.
    delete ArraySize;

    Require(']');

    const auto &End = PeekCurrent();

    if (End.Is(',') || // Function parameter.
        End.Is(')') || // Last function parameter.
        End.Is(';'))   // End of declaration.
      break;
  }

  return new ASTArrayDecl(DataType.Type, std::move(VariableName),
                          std::move(ArityList), DataType.LineNo,
                          DataType.ColumnNo);
}

ASTNode *Parser::ParseVarDecl() {
  const Token &DataType = ParseType();
  std::string VariableName = PeekNext().Data;
  const Token &Current = PeekNext();

  if (Current.Is('='))
    return new ASTVarDecl(DataType.Type, std::move(VariableName),
                          ParseLogicalOr(), DataType.LineNo, DataType.ColumnNo);

  // This is placed here because language supports nested functions.
  if (Current.Is('(')) {
    --TokenPtr; // Open paren.
    --TokenPtr; // Function name.
    --TokenPtr; // Data type.
    return ParseFunctionDecl();
  }

  if (Current.Is('[')) {
    --TokenPtr; // Open paren.
    --TokenPtr; // Declaration name.
    --TokenPtr; // Data type.
    return ParseArrayDecl();
  }

  weak::CompileError(Current.LineNo, Current.ColumnNo)
      << "Expected function, variable or array declaration";
  weak::UnreachablePoint();
}

ASTNode *Parser::ParseDecl() {
  switch (const Token &Current = PeekCurrent(); Current.Type) {
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
    weak::CompileError(Current.LineNo, Current.ColumnNo)
        << "Declaration expected";
    weak::UnreachablePoint();
  }
}

ASTNode *Parser::ParseStructDecl() {
  std::vector<ASTNode *> Decls;

  const auto &BeginOfDecl = Require(TOK_STRUCT);
  const auto &Name = Require(TOK_SYMBOL);

  Require('{');

  while (!TokenPtr->Is('}')) {
    Decls.push_back(ParseDecl());
    Require(';');
  }

  Require('}');

  return new ASTStructDecl(Name.Data, std::move(Decls), BeginOfDecl.LineNo,
                           BeginOfDecl.ColumnNo);
}

const Token &Parser::ParseType() {
  switch (const auto &T = PeekCurrent(); T.Type) {
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
  const Token &Current = PeekCurrent();
  if (Current.Type != TOK_VOID)
    return ParseType();
  PeekNext();
  return Current;
}

ASTNode *Parser::ParseDeclWithoutInitializer() {
  unsigned Offset = 0U;
  ++Offset; // Data type.
  ++Offset; // Parameter name.
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
    Require({')', ','});
    if ((TokenPtr - 1)->Is(')')) {
      /// Move back to token before '('.
      --TokenPtr;
      break;
    }
  }
  return List;
}

ASTCompoundStmt *Parser::ParseBlock() {
  if (LoopsDepth > 0)
    return ParseIterationStmtBlock();

  std::vector<ASTNode *> Statements;

  const Token &BeginOfBlock = Require('{');
  while (!PeekCurrent().Is('}')) {
    Statements.push_back(ParseStatement());
    switch (const ASTType Type = Statements.back()->GetASTType(); Type) {
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

  return new ASTCompoundStmt(std::move(Statements), BeginOfBlock.LineNo,
                             BeginOfBlock.ColumnNo);
}

ASTCompoundStmt *Parser::ParseIterationStmtBlock() {
  std::vector<ASTNode *> Statements;

  const Token &BeginOfBlock = Require('{');
  while (!PeekCurrent().Is('}')) {
    Statements.push_back(ParseLoopStatement());
    switch (const ASTType Type = Statements.back()->GetASTType(); Type) {
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

  return new ASTCompoundStmt(std::move(Statements), BeginOfBlock.LineNo,
                             BeginOfBlock.ColumnNo);
}

ASTNode *Parser::ParseStatement() {
  switch (const Token &Current = PeekCurrent(); Current.Type) {
    // case
  case TOK_IF:
    return ParseSelectionStatement();
  case TOK_FOR:
  case TOK_DO:
  case TOK_WHILE: // Fall through.
    return ParseIterationStatement();
  case TOK_RETURN:
    return ParseJumpStatement();
  case TOK_INT:
  case TOK_CHAR:
  case TOK_FLOAT:
  case TOK_STRING:
  case TOK_BOOLEAN:
  case TOK_SYMBOL: // Fall through.
    return ParseExpression();
  case TOK_INC:
  case TOK_DEC: // Fall through.
    return ParsePrefixUnary();
  default:
    weak::CompileError(Current.LineNo, Current.ColumnNo)
        << "Unexpected token: " << TokenToString(Current.Type);
    weak::UnreachablePoint();
  }
}

ASTNode *Parser::ParseSelectionStatement() {
  ASTNode *Condition{nullptr};
  ASTCompoundStmt *ThenBody{nullptr};
  ASTCompoundStmt *ElseBody{nullptr};

  const Token &BeginOfSelectionStmt = Require(TOK_IF);
  Require('(');
  Condition = ParseLogicalOr();
  Require(')');
  ThenBody = ParseBlock();

  if (Match(TOK_ELSE)) {
    ElseBody = ParseBlock();
    assert(ElseBody);
  }

  assert(ThenBody);

  return new ASTIfStmt(Condition, ThenBody, ElseBody,
                       BeginOfSelectionStmt.LineNo,
                       BeginOfSelectionStmt.ColumnNo);
}

ASTNode *Parser::ParseIterationStatement() {
  switch (const Token &Current = PeekCurrent(); Current.Type) {
  case TOK_FOR:
    return ParseForStatement();
  case TOK_DO:
    return ParseDoWhileStatement();
  case TOK_WHILE:
    return ParseWhileStatement();
  default:
    weak::UnreachablePoint("Should not reach here");
  }
}

ASTNode *Parser::ParseForStatement() {
  const Token &ForStmtBegin = Require(TOK_FOR);
  Require('(');

  ASTNode *Init{nullptr};
  if (!PeekNext().Is(';')) {
    --TokenPtr;
    Init = ParseExpression();
    PeekNext();
  }

  ASTNode *Condition{nullptr};
  if (!PeekNext().Is(';')) {
    --TokenPtr;
    Condition = ParseExpression();
    PeekNext();
  }

  ASTNode *Increment{nullptr};
  if (!PeekNext().Is(';')) {
    --TokenPtr;
    Increment = ParseExpression();
    PeekNext();
  }
  --TokenPtr;

  ++LoopsDepth;

  Require(')');
  auto *Body = ParseIterationStmtBlock();

  --LoopsDepth;

  return new ASTForStmt(Init, Condition, Increment, Body, ForStmtBegin.LineNo,
                        ForStmtBegin.ColumnNo);
}

ASTNode *Parser::ParseDoWhileStatement() {
  const Token &DoWhileBegin = Require(TOK_DO);

  ++LoopsDepth;

  auto *Body = ParseIterationStmtBlock();

  --LoopsDepth;

  Require(TOK_WHILE);

  Require('(');
  auto *Condition = ParseLogicalOr();
  Require(')');

  return new ASTDoWhileStmt(Body, Condition, DoWhileBegin.LineNo,
                            DoWhileBegin.ColumnNo);
}

ASTNode *Parser::ParseWhileStatement() {
  const Token &WhileBegin = Require(TOK_WHILE);
  Require('(');
  auto *Condition = ParseLogicalOr();
  Require(')');

  ++LoopsDepth;

  auto *Body = ParseIterationStmtBlock();

  --LoopsDepth;

  return new ASTWhileStmt(Condition, Body, WhileBegin.LineNo,
                          WhileBegin.ColumnNo);
}

ASTNode *Parser::ParseLoopStatement() {
  switch (const Token &Current = PeekNext(); Current.Type) {
  case TOK_BREAK:
    return new ASTBreakStmt(Current.LineNo, Current.ColumnNo);
  case TOK_CONTINUE:
    return new ASTContinueStmt(Current.LineNo, Current.ColumnNo);
  default:
    --TokenPtr;
    return ParseStatement();
  }
}

ASTNode *Parser::ParseJumpStatement() {
  const Token &ReturnStmt = Require(TOK_RETURN);
  if (Match(';')) {
    // This is `return;` case.
    // Rollback to allow match ';' in block parse function.
    --TokenPtr;
    return new ASTReturnStmt(nullptr, ReturnStmt.LineNo, ReturnStmt.ColumnNo);
  }
  // We want to forbid expressions like int var = var = var, so we
  // expect the first expression to have the precedence is lower than
  // the assignment operator.
  return new ASTReturnStmt(ParseExpression(), ReturnStmt.LineNo,
                           ReturnStmt.ColumnNo);
}

ASTNode *Parser::ParseArrayAccessOperator() {
  const Token &Symbol = PeekNext();

  Require('[');
  auto *Expr = ParseExpression();
  Require(']');

  return new ASTArrayAccess(Symbol.Data, Expr, Symbol.LineNo, Symbol.ColumnNo);
}

ASTNode *Parser::ParseExpression() {
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
    switch (const Token &Current = PeekNext(); Current.Type) {
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
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseAssignment(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_OR:
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseLogicalOr(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_AND:
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseLogicalAnd(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_BIT_OR:
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseInclusiveOr(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_XOR:
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseExclusiveOr(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_BIT_AND:
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseAnd(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_EQ:
    case TOK_NEQ: // Fall through.
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseEquality(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_GT:
    case TOK_LT:
    case TOK_GE:
    case TOK_LE: // Fall through.
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseRelational(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_SHL:
    case TOK_SHR: // Fall through.
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseShift(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_PLUS:
    case TOK_MINUS: // Fall through.
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseAdditive(),
                                   Current.LineNo, Current.ColumnNo);
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
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_STAR:
    case TOK_SLASH:
    case TOK_MOD: // Fall through.
      Expr = new ASTBinaryOperator(Current.Type, Expr, ParseMultiplicative(),
                                   Current.LineNo, Current.ColumnNo);
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
  switch (const Token Current = PeekNext(); Current.Type) {
  case TOK_INC:
  case TOK_DEC: // Fall through.
    return new ASTUnaryOperator(ASTUnaryOperator::UnaryType::PREFIX,
                                Current.Type, ParsePostfixUnary(),
                                Current.LineNo, Current.ColumnNo);
  default:
    // Rollback current token pointer because there's no unary operator.
    --TokenPtr;
    return ParsePostfixUnary();
  }
}

ASTNode *Parser::ParsePostfixUnary() {
  auto *Expr = ParsePrimary();
  while (true) {
    switch (const Token &Current = PeekNext(); Current.Type) {
    case TOK_INC:
    case TOK_DEC: // Fall through.
      Expr = new ASTUnaryOperator(ASTUnaryOperator::UnaryType::POSTFIX,
                                  Current.Type, Expr, Current.LineNo,
                                  Current.ColumnNo);
      continue;
    default:
      --TokenPtr;
      break;
    }
    break;
  }
  return Expr;
}

ASTNode *Parser::ParseSymbolProduction() {
  const Token &StartOfExpression = *(TokenPtr - 1);
  switch (const Token &Current = PeekCurrent(); Current.Type) {
  case TOK_OPEN_PAREN: {
    --TokenPtr;
    return ParseFunctionCall();
  }
  case TOK_OPEN_BOX_BRACKET: {
    --TokenPtr;
    return ParseArrayAccessOperator();
  }
  default:
    return new ASTSymbol(StartOfExpression.Data, StartOfExpression.LineNo,
                         StartOfExpression.ColumnNo);
  }
}

ASTNode *Parser::ParsePrimary() {
  switch (const Token &Current = PeekNext(); Current.Type) {
  case TOK_SYMBOL:
    return ParseSymbolProduction();
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
  switch (const Token &Current = PeekNext(); Current.Type) {
  case TOK_INTEGRAL_LITERAL:
    return new ASTIntegerLiteral(std::stoi(Current.Data), Current.LineNo,
                                 Current.ColumnNo);

  case TOK_FLOATING_POINT_LITERAL:
    return new ASTFloatingPointLiteral(std::stof(Current.Data), Current.LineNo,
                                       Current.ColumnNo);

  case TOK_STRING_LITERAL:
    return new ASTStringLiteral(Current.Data, Current.LineNo, Current.ColumnNo);

  case TOK_CHAR_LITERAL:
    return new ASTCharLiteral(Current.Data[0], Current.LineNo,
                              Current.ColumnNo);

  case TOK_FALSE:
  case TOK_TRUE:
    return new ASTBooleanLiteral(Current.Type == TOK_TRUE, Current.LineNo,
                                 Current.ColumnNo);

  default:
    weak::CompileError(Current.LineNo, Current.ColumnNo)
        << "Literal expected, got " << TokenToString(Current.Type);
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