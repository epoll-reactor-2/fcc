/* TypeAnalysis.cpp - Type checker.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/Analysis/TypeAnalysis.h"
#include "FrontEnd/AST/ASTArrayAccess.h"
#include "FrontEnd/AST/ASTArrayDecl.h"
#include "FrontEnd/AST/ASTBinary.h"
#include "FrontEnd/AST/ASTBool.h"
#include "FrontEnd/AST/ASTChar.h"
#include "FrontEnd/AST/ASTCompound.h"
#include "FrontEnd/AST/ASTFloat.h"
#include "FrontEnd/AST/ASTFunctionCall.h"
#include "FrontEnd/AST/ASTFunctionDecl.h"
#include "FrontEnd/AST/ASTFunctionPrototype.h"
#include "FrontEnd/AST/ASTNumber.h"
#include "FrontEnd/AST/ASTReturn.h"
#include "FrontEnd/AST/ASTString.h"
#include "FrontEnd/AST/ASTSymbol.h"
#include "FrontEnd/AST/ASTUnary.h"
#include "FrontEnd/AST/ASTVarDecl.h"
#include "FrontEnd/Lex/Token.h"
#include "Utility/Diagnostic.h"
#include "Utility/EnumOstreamOperators.h"
#include <cassert>

namespace weak {

TypeAnalysis::TypeAnalysis(ASTNode *Root)
    : mRoot(Root), mLastDataType(DT_UNKNOWN), mLastReturnDataType(DT_UNKNOWN) {}

void TypeAnalysis::Analyze() { mRoot->Accept(this); }

void TypeAnalysis::Visit(ASTCompound *Stmt) {
  mStorage.StartScope();
  for (ASTNode *S : Stmt->Stmts())
    S->Accept(this);
  mStorage.EndScope();
}

void TypeAnalysis::Visit(ASTBool *) { mLastDataType = DT_BOOL; }
void TypeAnalysis::Visit(ASTChar *) { mLastDataType = DT_CHAR; }
void TypeAnalysis::Visit(ASTFloat *) { mLastDataType = DT_FLOAT; }
void TypeAnalysis::Visit(ASTNumber *) { mLastDataType = DT_INT; }
void TypeAnalysis::Visit(ASTString *) { mLastDataType = DT_STRING; }

bool TypeAnalysis::CorrectBinaryOpsAnalysis(TokenType Op, DataType T) {
  bool CorrectOps = false;

  switch (Op) {
  case TOK_ASSIGN:
    /// We need only check if there are same types on assignment.
    [[fallthrough]];
  /// Integer and floats.
  case TOK_PLUS:
  case TOK_MINUS:
  case TOK_STAR:
  case TOK_SLASH:
  case TOK_LE:
  case TOK_LT:
  case TOK_GE:
  case TOK_GT:
  case TOK_EQ:
  case TOK_NEQ:
  case TOK_OR:
  case TOK_AND:
  case TOK_MUL_ASSIGN:
  case TOK_DIV_ASSIGN:
  case TOK_PLUS_ASSIGN:
  case TOK_MINUS_ASSIGN: /// Fall through.
    CorrectOps |= T == DT_INT;
    CorrectOps |= T == DT_CHAR;
    CorrectOps |= T == DT_BOOL;
    CorrectOps |= T == DT_FLOAT;
    break;
  /// Only integers.
  case TOK_BIT_OR:
  case TOK_BIT_AND:
  case TOK_XOR:
  case TOK_SHL:
  case TOK_SHR:
  case TOK_MOD_ASSIGN:
  case TOK_BIT_OR_ASSIGN:
  case TOK_BIT_AND_ASSIGN:
  case TOK_XOR_ASSIGN:
  case TOK_SHL_ASSIGN:
  case TOK_SHR_ASSIGN: /// Fall through.
    CorrectOps |= T == DT_INT;
    CorrectOps |= T == DT_CHAR;
    CorrectOps |= T == DT_BOOL;
    break;
  default:
    break;
  }

  return CorrectOps;
}

void TypeAnalysis::Visit(ASTBinary *Stmt) {
  Stmt->LHS()->Accept(this);
  DataType LType = mLastDataType;

  Stmt->RHS()->Accept(this);
  DataType RType = mLastDataType;

  bool AreSame = false;
  AreSame |= LType == DT_BOOL && RType == DT_BOOL;
  AreSame |= LType == DT_CHAR && RType == DT_CHAR;
  AreSame |= LType == DT_FLOAT && RType == DT_FLOAT;
  AreSame |= LType == DT_INT && RType == DT_INT;

  auto Op = Stmt->Operation();
  bool CorrectOps = CorrectBinaryOpsAnalysis(Op, LType);

  if (!AreSame || !CorrectOps)
    weak::CompileError(Stmt)
        << "Cannot apply `" << Op << "` to " << LType << " and " << RType;
}

void TypeAnalysis::Visit(ASTUnary *Stmt) {
  Stmt->Operand()->Accept(this);
  DataType T = mLastDataType;

  bool Allowed = false;
  Allowed |= T == DT_CHAR;
  Allowed |= T == DT_INT;

  if (!Allowed)
    weak::CompileError(Stmt)
        << "Cannot apply `" << Stmt->Operation() << "` to " << T;
}

void TypeAnalysis::Visit(ASTArrayDecl *Decl) {
  mStorage.Push(Decl->Name(), Decl->DataType(), Decl);
  mLastDataType = Decl->DataType();
}

void TypeAnalysis::Visit(ASTVarDecl *Decl) {
  if (auto *B = Decl->Body())
    B->Accept(this);
  mStorage.Push(Decl->Name(), Decl->DataType(), Decl);
  mLastDataType = Decl->DataType();
}

void TypeAnalysis::Visit(ASTArrayAccess *Stmt) {
  auto *Record = mStorage.Lookup(Stmt->Name())->AST;
  /// \todo: Get rid of `string` data type and introduce API for
  ///        C-style char arrays.
  if (!Record->Is(AST_ARRAY_DECL)) {
    auto *D = static_cast<ASTVarDecl *>(Record);
    if (D->DataType() != DT_STRING) {
      weak::CompileError(D) << "Cannot get index of non-array type";
    }
  }

  ASTArrayDecl *Array = static_cast<ASTArrayDecl *>(Record);

  Stmt->Index()->Accept(this);
  if (mLastDataType != DT_INT)
    weak::CompileError(Stmt->Index())
        << "Expected integer as array index, got " << mLastDataType;

  if (auto *I = Stmt->Index(); I->Is(AST_INTEGER_LITERAL)) {
    signed Index = static_cast<ASTNumber *>(I)->Value();
    signed ArraySize = Array->ArityList()[0];

    if (Index < 0)
      weak::CompileError(I) << "Array index less than zero";

    if (Index >= ArraySize)
      weak::CompileError(I) << "Out of range! Index (which is " << Index
                            << ") >= array size (which is " << ArraySize << ")";
  }

  mLastDataType = Array->DataType();
}

void TypeAnalysis::Visit(ASTSymbol *Stmt) {
  mLastDataType = mStorage.Lookup(Stmt->Name())->Type;
}

void TypeAnalysis::Visit(ASTFunctionDecl *Decl) {
  mStorage.StartScope();
  /// This is to have function in recursive calls.
  mStorage.Push(Decl->Name(), DT_FUNC, Decl);

  for (auto *Arg : Decl->Args()) {
    if (Arg->Is(AST_VAR_DECL)) {
      auto *D = static_cast<ASTVarDecl *>(Arg);
      mStorage.Push(D->Name(), D->DataType(), D);
    }

    if (Arg->Is(AST_ARRAY_DECL)) {
      auto *D = static_cast<ASTArrayDecl *>(Arg);
      mStorage.Push(D->Name(), D->DataType(), D);
    }
  }

  Decl->Body()->Accept(this);

  if (auto RT = Decl->ReturnType(); RT != DT_VOID)
    if (mLastReturnDataType != RT)
      weak::CompileError(Decl)
          << "Cannot return " << mLastReturnDataType << " instead of " << RT;

  mStorage.EndScope();
  /// This is to have function outside.
  mStorage.Push(Decl->Name(), DT_FUNC, Decl);
}

void TypeAnalysis::Visit(ASTFunctionPrototype *Decl) {
  mStorage.Push(Decl->Name(), DT_FUNC, Decl);
}

static const std::string &GetFunArgName(ASTNode *Stmt) {
  if (Stmt->Is(AST_VAR_DECL))
    return static_cast<ASTVarDecl *>(Stmt)->Name();

  if (Stmt->Is(AST_ARRAY_DECL))
    return static_cast<ASTArrayDecl *>(Stmt)->Name();

  Unreachable();
}

template <typename ASTFun>
void TypeAnalysis::CallArgumentsAnalysis(ASTNode *Decl,
                                         const std::vector<ASTNode *> &Args) {
  const auto &DeclArgs = static_cast<ASTFun *>(Decl)->Args();
  assert(DeclArgs.size() == Args.size() &&
         "Argument sizes should be checked in function analyzer");

  for (unsigned I{0U}; I < Args.size(); ++I) {
    DeclArgs[I]->Accept(this);
    DataType LType = mLastDataType;
    Args[I]->Accept(this);
    DataType RType = mLastDataType;

    if (LType != RType)
      weak::CompileError(Args[I])
          << "For argument `" << GetFunArgName(DeclArgs[I]) << "` got " << LType
          << ", but expected " << RType;
  }
}

template void TypeAnalysis::CallArgumentsAnalysis<ASTFunctionDecl>(
    ASTNode *Decl, const std::vector<ASTNode *> &Args);
template void TypeAnalysis::CallArgumentsAnalysis<ASTFunctionPrototype>(
    ASTNode *Decl, const std::vector<ASTNode *> &Args);

void TypeAnalysis::Visit(ASTFunctionCall *Stmt) {
  auto *Decl = mStorage.Lookup(Stmt->Name())->AST;

  if (Decl->Is(AST_FUNCTION_DECL))
    CallArgumentsAnalysis<ASTFunctionDecl>(Decl, Stmt->Args());

  if (Decl->Is(AST_FUNCTION_PROTOTYPE))
    CallArgumentsAnalysis<ASTFunctionPrototype>(Decl, Stmt->Args());
}

void TypeAnalysis::Visit(ASTReturn *Decl) {
  Decl->Operand()->Accept(this);
  mLastReturnDataType = mLastDataType;
}

} // namespace weak