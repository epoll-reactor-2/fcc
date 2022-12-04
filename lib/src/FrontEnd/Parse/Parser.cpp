/* Parser.cpp - Implementation of syntax analyzer.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Parse/Parser.h"
#include "FrontEnd/AST/AST.h"
#include "Utility/Diagnostic.h"
#include "Utility/EnumOstreamOperators.h"
#include "Utility/Unreachable.h"
#include <cassert>

namespace weak {

static DataType TokenToDT(TokenType T) {
  switch (T) {
  case TOK_VOID:   return DT_VOID;
  case TOK_INT:    return DT_INT;
  case TOK_FLOAT:  return DT_FLOAT;
  case TOK_CHAR:   return DT_CHAR;
  case TOK_STRING: return DT_STRING;
  case TOK_BOOL:   return DT_BOOL;
  case TOK_STRUCT: return DT_STRUCT;
  default:         Unreachable("Expected data type.");
  }
}

Parser::Parser(const Token *BufStart, const Token *BufEnd)
  : mBufStart(BufStart)
  , mBufEnd(BufEnd)
  , mTokenPtr(mBufStart)
  , mLoopsDepth(0U) {
  assert(mBufStart);
  assert(mBufEnd);
  assert(mBufStart <= mBufEnd);
}

std::unique_ptr<ASTCompound> Parser::Parse() {
  std::vector<ASTNode *> Stmts;
  while (mTokenPtr <= mBufEnd) {
    switch (const Token &T = PeekCurrent(); T.Type) {
    case TOK_STRUCT:
      Stmts.push_back(ParseStructDecl());
      break;
    case TOK_VOID:
    case TOK_INT:
    case TOK_CHAR:
    case TOK_STRING:
    case TOK_FLOAT:
    case TOK_BOOL: // Fall through.
      Stmts.push_back(ParseFunctionDecl());
      break;
    default:
      weak::CompileError(T.LineNo, T.ColumnNo)
        << "Functions as global statements supported only";
      break;
    }
  }
  return std::unique_ptr<ASTCompound>(
    new ASTCompound(
      std::move(Stmts),
      /*LineNo=*/0,
      /*ColumnNo=*/0
    )
  );
}

ASTNode *Parser::ParseFunctionDecl() {
  /// Guaranteed data type, no checks needed.
  LocalizedDataType ReturnType = ParseReturnType();
  const Token &FunctionName = PeekNext();

  if (FunctionName.Type != TOK_SYMBOL)
    weak::CompileError(FunctionName.LineNo, FunctionName.ColumnNo)
      << "Function name expected";

  Require('(');
  auto ParameterList = ParseParameterList();
  Require(')');

  if (PeekCurrent().Is('{')) {
    auto *Block = ParseBlock();

    return new ASTFunctionDecl(
      ReturnType.DT,
      std::string(FunctionName.Data),
      std::move(ParameterList),
      Block,
      ReturnType.LineNo,
      ReturnType.ColumnNo
    );
  }

  Require(';');
  return new ASTFunctionPrototype(
    ReturnType.DT,
    std::string(FunctionName.Data),
    std::move(ParameterList),
    ReturnType.LineNo,
    ReturnType.ColumnNo
  );
}

ASTNode *Parser::ParseFunctionCall() {
  const Token &FunctionName = PeekNext();
  std::string Name = FunctionName.Data;
  std::vector<ASTNode *> Arguments;

  Require('(');

  auto Finish = [&] {
    return new ASTFunctionCall(
      std::move(Name),
      std::move(Arguments),
      FunctionName.LineNo,
      FunctionName.ColumnNo
    );
  };

  if (PeekNext().Is(')'))
    return Finish();

  --mTokenPtr;
  while (!PeekCurrent().Is(')')) {
    Arguments.push_back(ParseLogicalOr());
    if (Require({')', ','}).Is(')'))
      /// Move back to token before '(' and break on next iteration.
      --mTokenPtr;
  }

  Require(')');

  return Finish();
}

ASTNode *Parser::ParseStructVarDecl() {
  const Token &Type = Require(TOK_SYMBOL);
  const Token &VariableName = Require(TOK_SYMBOL);

  return new ASTVarDecl(
    DT_STRUCT,
    Type.Data,
    VariableName.Data,
    /*Body=*/nullptr,
    Type.LineNo,
    Type.ColumnNo
  );
}

ASTNode *Parser::ParseVarDeclWithoutInitializer() {
  const auto &DataType = ParseType();
  const Token &VariableName = PeekNext();

  if (VariableName.Type != TOK_SYMBOL)
    weak::CompileError(VariableName.LineNo, VariableName.ColumnNo)
      << "Variable name expected";

  return new ASTVarDecl(
    DataType.DT,
    std::string(VariableName.Data),
    /*Body=*/nullptr,
    DataType.LineNo,
    DataType.ColumnNo
  );
}

ASTNode *Parser::ParseArrayDecl() {
  const auto &DataType = ParseType();
  std::string VariableName = PeekNext().Data;
  const Token &T = PeekNext();

  std::vector<unsigned> ArityList;

  --mTokenPtr;

  if (!(mTokenPtr)->Is('['))
    weak::CompileError(DataType.LineNo, DataType.ColumnNo)
      << "`[` expected";

  while (PeekCurrent().Is('[')) {
    Require('[');
    auto *Constant = ParseConstant();

    if (!Constant->Is(AST_INTEGER_LITERAL))
      weak::CompileError(T.LineNo, T.ColumnNo)
        << "Integer size declarator expected";

    auto *ArraySize = static_cast<ASTNumber *>(Constant);

    ArityList.push_back(ArraySize->Value());

    /// We need only number, not whole AST node, so we can
    /// get rid of it.
    delete ArraySize;
    Require(']');
  }

  return new ASTArrayDecl(
    DataType.DT,
    std::move(VariableName),
    std::move(ArityList),
    DataType.LineNo,
    DataType.ColumnNo
  );
}

ASTNode *Parser::ParseVarDecl() {
  const auto &DataType = ParseType();
  std::string VariableName = PeekNext().Data;
  const Token &T = PeekNext();

  if (T.Is('='))
    return new ASTVarDecl(
      DataType.DT,
      std::move(VariableName),
      ParseLogicalOr(),
      DataType.LineNo,
      DataType.ColumnNo
    );

  /// This is placed here because language supports nested functions.
  if (T.Is('(')) {
    --mTokenPtr; /// Open paren.
    --mTokenPtr; /// Function name.
    --mTokenPtr; /// Data type.
    return ParseFunctionDecl();
  }

  if (T.Is('[')) {
    --mTokenPtr; /// Open paren.
    --mTokenPtr; /// Declaration name.
    --mTokenPtr; /// Data type.
    return ParseArrayDecl();
  }

  weak::CompileError(T.LineNo, T.ColumnNo)
    << "Expected function, variable or array declaration";
  Unreachable("Should not reach there.");
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
  case TOK_BOOL: // Fall through.
    return ParseDeclWithoutInitializer();
  default:
    weak::CompileError(T.LineNo, T.ColumnNo) << "Declaration expected";
    Unreachable("Should not reach there.");
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

  return new ASTStructDecl(
    Name.Data,
    std::move(Decls),
    Start.LineNo,
    Start.ColumnNo
  );
}

ASTNode *Parser::ParseStructFieldAccess() {
  const Token &Symbol = Require(TOK_SYMBOL);
  const Token &Next = PeekNext();

  if (Next.Type == TOK_DOT)
    return new ASTMemberAccess(
      new ASTSymbol(Symbol.Data, Symbol.LineNo, Symbol.ColumnNo),
      ParseStructFieldAccess(),
      Symbol.LineNo,
      Symbol.ColumnNo
    );

  --mTokenPtr;
  return new ASTSymbol(Symbol.Data, Symbol.LineNo, Symbol.ColumnNo);
}

Parser::LocalizedDataType Parser::ParseType() {
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_INT:
  case TOK_FLOAT:
  case TOK_CHAR:
  case TOK_STRING:
  case TOK_BOOL: // Fall through.
    PeekNext();
    return {T.LineNo, T.ColumnNo, TokenToDT(T.Type)};
  default:
    weak::CompileError(T.LineNo, T.ColumnNo)
      << "Data type expected, got " << T.Type;
    Unreachable("Should not reach there.");
  }
}

Parser::LocalizedDataType Parser::ParseReturnType() {
  const Token &T = PeekCurrent();
  if (T.Type != TOK_VOID)
    return ParseType();
  PeekNext();
  return {T.LineNo, T.ColumnNo, TokenToDT(T.Type)};
}

ASTNode *Parser::ParseDeclWithoutInitializer() {
  unsigned Offset = 0U;
  ++Offset; /// Data type.
  ++Offset; /// Parameter name.

  if ((mTokenPtr + Offset)->Is('['))
    return ParseArrayDecl();

  if (PeekCurrent().Is(TOK_SYMBOL))
    return ParseStructVarDecl();

  /// Built-in data types.
  return ParseVarDeclWithoutInitializer();
}

std::vector<ASTNode *> Parser::ParseParameterList() {
  std::vector<ASTNode *> List;
  if (PeekNext().Is(')')) {
    --mTokenPtr;
    return List;
  }

  --mTokenPtr;
  while (!PeekCurrent().Is(')')) {
    List.push_back(ParseDeclWithoutInitializer());
    if (Require({')', ','}).Is(')')) {
      /// Move back to token before '('.
      --mTokenPtr;
      break;
    }
  }
  return List;
}

ASTCompound *Parser::ParseBlock() {
  if (mLoopsDepth > 0)
    return ParseIterationBlock();

  std::vector<ASTNode *> Stmts;
  const Token &Start = Require('{');

  while (!PeekCurrent().Is('}')) {
    Stmts.push_back(ParseStmt());
    switch (ASTType Type = Stmts.back()->Type(); Type) {
    case AST_BINARY:
    case AST_POSTFIX_UNARY:
    case AST_PREFIX_UNARY:
    case AST_SYMBOL:
    case AST_RETURN_STMT:
    case AST_DO_WHILE_STMT:
    case AST_VAR_DECL:
    case AST_ARRAY_DECL:
    case AST_ARRAY_ACCESS:
    case AST_MEMBER_ACCESS:
    case AST_FUNCTION_CALL: // Fall through.
      Require(';');
      break;
    default:
      break;
    }
  }
  Require('}');

  return new ASTCompound(std::move(Stmts), Start.LineNo, Start.ColumnNo);
}

ASTCompound *Parser::ParseIterationBlock() {
  std::vector<ASTNode *> Stmts;
  const Token &Start = Require('{');

  while (!PeekCurrent().Is('}')) {
    Stmts.push_back(ParseLoopStmt());
    switch (ASTType Type = Stmts.back()->Type(); Type) {
    case AST_BINARY:
    case AST_POSTFIX_UNARY:
    case AST_PREFIX_UNARY:
    case AST_SYMBOL:
    case AST_RETURN_STMT:
    case AST_BREAK_STMT:
    case AST_CONTINUE_STMT:
    case AST_DO_WHILE_STMT:
    case AST_VAR_DECL:
    case AST_MEMBER_ACCESS:
    case AST_FUNCTION_CALL: // Fall through.
      Require(';');
      break;
    default:
      break;
    }
  }
  Require('}');

  return new ASTCompound(std::move(Stmts), Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseStmt() {
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_OPEN_CURLY_BRACKET:
    return ParseBlock();
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
  case TOK_BOOL:
  case TOK_SYMBOL: // Fall through.
    return ParseExpr();
  case TOK_INC:
  case TOK_DEC: // Fall through.
    return ParsePrefixUnary();
  default:
    weak::CompileError(T.LineNo, T.ColumnNo) << "Unexpected token: " << T.Type;
    Unreachable("Should not reach there.");
  }
}

ASTNode *Parser::ParseSelectionStmt() {
  ASTNode *Condition{nullptr};
  ASTCompound *ThenBody{nullptr};
  ASTCompound *ElseBody{nullptr};
  const Token &Start = Require(TOK_IF);

  Require('(');
  Condition = ParseLogicalOr();
  Require(')');
  ThenBody = ParseBlock();

  if (Match(TOK_ELSE))
    ElseBody = ParseBlock();

  return new ASTIf(
    Condition,
    ThenBody,
    ElseBody,
    Start.LineNo,
    Start.ColumnNo
  );
}

ASTNode *Parser::ParseIterationStmt() {
  switch (const Token &T = PeekCurrent(); T.Type) {
  case TOK_FOR:
    return ParseFor();
  case TOK_DO:
    return ParseDoWhile();
  case TOK_WHILE:
    return ParseWhile();
  default:
    Unreachable("Expected iteration statement.");
  }
}

ASTNode *Parser::ParseFor() {
  const Token &Start = Require(TOK_FOR);
  Require('(');

  ASTNode *Init{nullptr};
  if (!PeekNext().Is(';')) {
    --mTokenPtr;
    Init = ParseExpr();
    PeekNext();
  }

  ASTNode *Condition{nullptr};
  if (!PeekNext().Is(';')) {
    --mTokenPtr;
    Condition = ParseExpr();
    PeekNext();
  }

  ASTNode *Increment{nullptr};
  if (!PeekNext().Is(')')) {
    --mTokenPtr;
    Increment = ParseExpr();
    PeekNext();
  }
  --mTokenPtr;

  ++mLoopsDepth;

  Require(')');
  auto *Body = ParseBlock();

  --mLoopsDepth;

  return new ASTFor(
    Init,
    Condition,
    Increment,
    Body,
    Start.LineNo,
    Start.ColumnNo
  );
}

ASTNode *Parser::ParseDoWhile() {
  const Token &Start = Require(TOK_DO);

  ++mLoopsDepth;

  auto *Body = ParseBlock();

  --mLoopsDepth;

  Require(TOK_WHILE);

  Require('(');
  auto *Condition = ParseLogicalOr();
  Require(')');

  return new ASTDoWhile(Body, Condition, Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseWhile() {
  const Token &Start = Require(TOK_WHILE);
  Require('(');
  auto *Condition = ParseLogicalOr();
  Require(')');

  ++mLoopsDepth;

  auto *Body = ParseBlock();

  --mLoopsDepth;

  return new ASTWhile(Condition, Body, Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseLoopStmt() {
  switch (const Token &T = PeekNext(); T.Type) {
  case TOK_BREAK:
    return new ASTBreak(T.LineNo, T.ColumnNo);
  case TOK_CONTINUE:
    return new ASTContinue(T.LineNo, T.ColumnNo);
  default:
    --mTokenPtr;
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
    --mTokenPtr;
  /// We want to forbid expressions like int var = var = var, so we
  /// expect the first expression to have the precedence is lower than
  /// the assignment operator.
  return new ASTReturn(Body, Start.LineNo, Start.ColumnNo);
}

ASTNode *Parser::ParseArrayAccess() {
  const Token &Symbol = PeekNext();

  if (!(mTokenPtr)->Is('['))
    weak::CompileError(Symbol.LineNo, Symbol.ColumnNo)
      << "`[` expected";

  std::vector<ASTNode *> AccessList;

  while (PeekCurrent().Is('[')) {
    Require('[');
    AccessList.push_back(ParseExpr());
    Require(']');
  }

  return new ASTArrayAccess(
    Symbol.Data,
    std::move(AccessList),
    Symbol.LineNo,
    Symbol.ColumnNo
  );
}

ASTNode *Parser::ParseExpr() {
  switch (PeekCurrent().Type) {
  case TOK_INT:
  case TOK_CHAR:
  case TOK_FLOAT:
  case TOK_STRING:
  case TOK_BOOL: // Fall through.
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
      Expr = new ASTBinary(T.Type, Expr, ParseAssignment(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseLogicalOr(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseLogicalAnd(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr =
          new ASTBinary(T.Type, Expr, ParseInclusiveOr(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr =
          new ASTBinary(T.Type, Expr, ParseExclusiveOr(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseAnd(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseEquality(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseRelational(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseShift(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseAdditive(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
      Expr = new ASTBinary(T.Type, Expr, ParseMultiplicative(), T.LineNo, T.ColumnNo);
      continue;
    default:
      --mTokenPtr;
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
    return new ASTUnary(
      ASTUnary::PREFIX,
      T.Type,
      ParsePostfixUnary(),
      T.LineNo,
      T.ColumnNo
    );
  default:
    /// Rollback current token pointer because there's no unary operator.
    --mTokenPtr;
    return ParsePostfixUnary();
  }
}

ASTNode *Parser::ParsePostfixUnary() {
  auto* Expr = ParsePrimary();
  switch (const Token& T = PeekNext(); T.Type) {
  case TOK_INC:
  case TOK_DEC: // Fall through.
    return new ASTUnary(
      ASTUnary::POSTFIX,
      T.Type, Expr,
      T.LineNo,
      T.ColumnNo
    );
  default:
    --mTokenPtr;
    return Expr;
  }
}

ASTNode *Parser::ParseSymbol() {
  const Token &Start = *(mTokenPtr - 1);
  switch (PeekCurrent().Type) {
  /// symbol(
  case TOK_OPEN_PAREN: {
    --mTokenPtr;
    return ParseFunctionCall();
  }
  /// symbol[
  case TOK_OPEN_BOX_BRACKET: {
    --mTokenPtr;
    return ParseArrayAccess();
  }
  /// symbol symbol
  case TOK_SYMBOL: {
    --mTokenPtr;
    return ParseStructVarDecl();
  }
  /// symbol.
  case TOK_DOT: {
    --mTokenPtr;
    return ParseStructFieldAccess();
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
    --mTokenPtr;
    return ParseConstant();
  }
}

ASTNode *Parser::ParseConstant() {
  switch (const Token &T = PeekNext(); T.Type) {
  case TOK_INTEGRAL_LITERAL:
    return new ASTNumber(std::stoi(T.Data), T.LineNo, T.ColumnNo);

  case TOK_FLOATING_POINT_LITERAL:
    return new ASTFloat(std::stof(T.Data), T.LineNo, T.ColumnNo);

  case TOK_STRING_LITERAL:
    return new ASTString(T.Data, T.LineNo, T.ColumnNo);

  case TOK_CHAR_LITERAL:
    return new ASTChar(T.Data[0], T.LineNo, T.ColumnNo);

  case TOK_FALSE:
  case TOK_TRUE:
    return new ASTBool(T.Is(TOK_TRUE), T.LineNo, T.ColumnNo);

  default:
    weak::CompileError(T.LineNo, T.ColumnNo)
      << "Literal expected, got " << T.Type;
    Unreachable("Should not reach there.");
  }
}

const Token &Parser::PeekNext() {
  AssertNotBufEnd();
  return *mTokenPtr++;
}

const Token &Parser::PeekCurrent() const {
  AssertNotBufEnd();
  return *mTokenPtr;
}

bool Parser::Match(const std::vector<TokenType> &Expected) {
  AssertNotBufEnd();
  for (TokenType Token : Expected) {
    if (mTokenPtr > mBufEnd)
      return false;
    if (PeekCurrent().Is(Token)) {
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

bool Parser::Match(char Expected) {
  return Match(CharToToken(Expected));
}

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
    return *(mTokenPtr - 1);

  weak::CompileError(mTokenPtr->LineNo, mTokenPtr->ColumnNo)
    << "Expected " << TokensToString(Expected)
    << ", got " << mTokenPtr->Type;
  Unreachable("Should not reach there.");
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
  if (mTokenPtr > mBufEnd)
    weak::CompileError(mTokenPtr->LineNo, mTokenPtr->LineNo)
      << "End of buffer reached";
}

} // namespace weak