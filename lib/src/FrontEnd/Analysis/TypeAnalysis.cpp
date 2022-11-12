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
#include <cassert>

namespace weak {

TypeAnalysis::TypeAnalysis(ASTNode *Root)
    : mRoot(Root), mLastDataType(DT_UNKNOWN), mLastReturnDataType(DT_UNKNOWN) {}

void TypeAnalysis::Analyze() { mRoot->Accept(this); }

void TypeAnalysis::Visit(ASTBool *) { mLastDataType = DT_BOOL; }
void TypeAnalysis::Visit(ASTChar *) { mLastDataType = DT_CHAR; }
void TypeAnalysis::Visit(ASTFloat *) { mLastDataType = DT_FLOAT; }
void TypeAnalysis::Visit(ASTNumber *) { mLastDataType = DT_INT; }
void TypeAnalysis::Visit(ASTString *) { mLastDataType = DT_STRING; }

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

  if (!AreSame)
    weak::CompileError(Stmt)
        << "Cannot apply `" << TokenToString(Stmt->Operation()) << "` to "
        << DataTypeToString(LType) << " and " << DataTypeToString(RType);
}

void TypeAnalysis::Visit(ASTUnary *Stmt) {
  Stmt->Operand()->Accept(this);
  DataType T = mLastDataType;

  bool Allowed = false;
  Allowed |= T == DT_CHAR;
  Allowed |= T == DT_INT;

  if (!Allowed)
    weak::CompileError(Stmt)
        << "Cannot apply `" << TokenToString(Stmt->Operation()) << "` to "
        << DataTypeToString(T);
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
  if (!Record->Is(AST_ARRAY_DECL))
    weak::CompileError(Record) << "Cannot get index of non-array type";

  ASTArrayDecl *Array = static_cast<ASTArrayDecl *>(Record);

  Stmt->Index()->Accept(this);
  if (mLastDataType != DT_INT)
    weak::CompileError(Stmt->Index()) << "Expected integer as array index, got "
                                      << DataTypeToString(mLastDataType);

  if (auto *I = Stmt->Index(); I->Is(AST_INTEGER_LITERAL)) {
    signed Index = static_cast<ASTNumber *>(I)->Value();
    signed ArraySize = Array->ArityList()[0];

    if (Index < 0)
      weak::CompileError(I) << "Array index less than zero";

    if (Index >= ArraySize)
      weak::CompileError(I) << "Out of range! Index (which is " << Index
                            << ") >= array size (which is " << ArraySize << ")";
  }
}

void TypeAnalysis::Visit(ASTSymbol *Stmt) {
  mLastDataType = mStorage.Lookup(Stmt->Name())->Type;
}

void TypeAnalysis::Visit(ASTFunctionDecl *Decl) {
  Decl->Body()->Accept(this);

  if (auto RT = Decl->ReturnType(); RT != DT_VOID)
    if (mLastReturnDataType != RT)
      weak::CompileError(Decl)
          << "Cannot return " << DataTypeToString(mLastReturnDataType)
          << " instead of " << DataTypeToString(RT);

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
void TypeAnalysis::DoCallArgumentsAnalysis(ASTNode *Decl,
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
          << "For argument `" << GetFunArgName(DeclArgs[I]) << "` got "
          << DataTypeToString(LType) << ", but expected "
          << DataTypeToString(RType);
  }
}

template void TypeAnalysis::DoCallArgumentsAnalysis<ASTFunctionDecl>(
    ASTNode *, const std::vector<ASTNode *> &);
template void TypeAnalysis::DoCallArgumentsAnalysis<ASTFunctionPrototype>(
    ASTNode *, const std::vector<ASTNode *> &);

void TypeAnalysis::Visit(ASTFunctionCall *Stmt) {
  auto *Decl = mStorage.Lookup(Stmt->Name())->AST;

  if (Decl->Is(AST_FUNCTION_DECL))
    DoCallArgumentsAnalysis<ASTFunctionDecl>(Decl, Stmt->Args());

  if (Decl->Is(AST_FUNCTION_PROTOTYPE))
    DoCallArgumentsAnalysis<ASTFunctionPrototype>(Decl, Stmt->Args());

  Unreachable();
}

void TypeAnalysis::Visit(ASTReturn *Decl) {
  Decl->Operand()->Accept(this);
  mLastReturnDataType = mLastDataType;
}

} // namespace weak