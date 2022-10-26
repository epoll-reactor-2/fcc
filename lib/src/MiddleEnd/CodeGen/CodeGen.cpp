/* CodeGen.cpp - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/CodeGen.hpp"

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
#include "FrontEnd/AST/ASTReturnStmt.hpp"
#include "FrontEnd/AST/ASTStringLiteral.hpp"
#include "FrontEnd/AST/ASTSymbol.hpp"
#include "FrontEnd/AST/ASTUnaryOperator.hpp"
#include "FrontEnd/AST/ASTVarDecl.hpp"
#include "FrontEnd/AST/ASTWhileStmt.hpp"
#include "MiddleEnd/CodeGen/ScalarExprEmitter.hpp"
#include "MiddleEnd/CodeGen/TypeCheck.hpp"
#include "MiddleEnd/CodeGen/TypeResolver.hpp"
#include "Utility/Diagnostic.hpp"
#include "llvm/ADT/APFloat.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"

namespace weak {
namespace {

/// Create function header (without body) from AST.
template <typename ASTFunctionDeclOrPrototype> class FunctionBuilder {
public:
  FunctionBuilder(llvm::LLVMContext &C, llvm::Module &M,
                  const ASTFunctionDeclOrPrototype *TheDecl)
      : Ctx(C), Module(M), Decl(TheDecl) {}

  llvm::Function *BuildSignature() {
    llvm::FunctionType *Signature = CreateSignature();
    /// \todo: Always external linkage? Come here after making multiple files
    ///        compilation.
    llvm::Function *Func = llvm::Function::Create(
        Signature, llvm::Function::ExternalLinkage, Decl->GetName(), &Module);

    unsigned Idx{0U};
    for (llvm::Argument &Arg : Func->args())
      Arg.setName(ExtractSymbol(Decl->GetArguments()[Idx++]));

    return Func;
  }

private:
  llvm::FunctionType *CreateSignature() {
    TypeResolver TypeResolver(Ctx);
    llvm::SmallVector<llvm::Type *, 16> ArgTypes;

    for (const auto &ArgAST : Decl->GetArguments())
      ArgTypes.push_back(ResolveParamType(ArgAST));

    llvm::FunctionType *Signature = llvm::FunctionType::get(
        /// Return type.
        TypeResolver.Resolve(Decl->GetReturnType()),
        /// Arguments.
        ArgTypes,
        /// Variadic parameters?
        false);

    return Signature;
  }

  llvm::Type *ResolveParamType(const ASTNode *ArgAST) {
    const auto ASTType = ArgAST->GetASTType();
    AssertDeclaration(ASTType);

    TypeResolver TypeResolver(Ctx);
    if (ASTType == AST_VAR_DECL)
      /// Variable.
      return TypeResolver.ResolveExceptVoid(ArgAST);

    /// Array.
    const auto *ArrayDecl = static_cast<const ASTArrayDecl *>(ArgAST);
    llvm::Type *UnderlyingType =
        TypeResolver.ResolveExceptVoid(ArrayDecl->GetDataType());
    return llvm::PointerType::get(UnderlyingType, /*AddressSpace=*/0);
  }

  const std::string &ExtractSymbol(const ASTNode *Node) {
    AssertDeclaration(Node->GetASTType());
    const auto *VarDecl = static_cast<const ASTVarDecl *>(Node);
    return VarDecl->GetSymbolName();
  }

  void AssertDeclaration(ASTType Type) {
    if (Type != AST_VAR_DECL && Type != AST_ARRAY_DECL)
      weak::UnreachablePoint("wrong AST nodes passed as function parameters");
  }

  llvm::LLVMContext &Ctx;
  llvm::Module &Module;
  const ASTFunctionDeclOrPrototype *Decl;
};

} // namespace
} // namespace weak

namespace weak {
namespace {

/// Create string literal (actually an array of 8-bit integers).
class StringBuilder {
public:
  StringBuilder(llvm::Module &M, llvm::IRBuilder<> &I)
      : Module(M), IRBuilder(I) {}

  llvm::Constant *BuildLiteral(std::string_view Data) {
    llvm::Constant *DataArray = CreateDataArray(Data);

    llvm::GlobalVariable *GlobalVar = new llvm::GlobalVariable(
        Module, DataArray->getType(), true,
        llvm::GlobalVariable::ExternalLinkage, DataArray);

    return llvm::ConstantExpr::getBitCast(
        GlobalVar, IRBuilder.getInt8Ty()->getPointerTo());
  }

private:
  llvm::Constant *CreateDataArray(std::string_view Data) {
    llvm::SmallVector<llvm::Constant *> Chars;
    Chars.reserve(Data.size());

    for (char C : Data)
      Chars.push_back(IRBuilder.getInt8(C));

    /// Since we are working with libc, we are expecting, that all strings
    /// will be ended with '\0'.
    Chars.push_back(CreateNullTerminator());

    size_t ArraySize = Chars.size();
    llvm::Constant *Array = llvm::ConstantArray::get(
        llvm::ArrayType::get(IRBuilder.getInt8Ty(), ArraySize),
        std::move(Chars));

    return Array;
  }

  llvm::Constant *CreateNullTerminator() { return IRBuilder.getInt8('\0'); }

  llvm::Module &Module;
  llvm::IRBuilder<> &IRBuilder;
};

} // namespace

namespace {

class AssignmentIRBuilder {
public:
  AssignmentIRBuilder(llvm::IRBuilder<> &TheIRBuilder,
                      const DeclsStorage &TheDeclStorage)
      : IRBuilder(TheIRBuilder), DeclStorage(TheDeclStorage) {}

  void Build(const ASTBinaryOperator *Stmt, llvm::Value *RHS,
             llvm::Value *ArrayPtr) {
    auto *LHS = Stmt->GetLHS();

    if (LHS->GetASTType() == AST_ARRAY_ACCESS)
      BuildArrayAssignment(RHS, ArrayPtr);
    else
      BuildRegularAssignment(LHS, RHS);
  }

private:
  void BuildArrayAssignment(llvm::Value *RHS, llvm::Value *ArrayPtr) {
    IRBuilder.CreateStore(RHS, ArrayPtr);
  }

  void BuildRegularAssignment(const ASTNode *LHS, llvm::Value *RHS) {
    const auto *Symbol = static_cast<const ASTSymbol *>(LHS);
    llvm::AllocaInst *Variable = DeclStorage.Lookup(Symbol->GetName());
    IRBuilder.CreateStore(RHS, Variable);
  }

  llvm::IRBuilder<> &IRBuilder;
  const DeclsStorage &DeclStorage;
};

} // namespace

CodeGen::CodeGen(ASTNode *TheRoot)
    : Root(TheRoot), DeclStorage(), LastInstr(nullptr), LastArrayPtr(nullptr),
      IRCtx(), IRModule("LLVM Module", IRCtx), IRBuilder(IRCtx) {}

void CodeGen::CreateCode() { Root->Accept(this); }

void CodeGen::Visit(const ASTBooleanLiteral *Stmt) {
  LastInstr = IRBuilder.getInt1(Stmt->GetValue());
}

void CodeGen::Visit(const ASTCharLiteral *Stmt) {
  LastInstr = IRBuilder.getInt8(Stmt->GetValue());
}

void CodeGen::Visit(const ASTIntegerLiteral *Stmt) {
  LastInstr = IRBuilder.getInt32(Stmt->GetValue());
}

void CodeGen::Visit(const ASTFloatingPointLiteral *Stmt) {
  llvm::APFloat Float(Stmt->GetValue());
  LastInstr = llvm::ConstantFP::get(IRCtx, Float);
}

void CodeGen::Visit(const ASTStringLiteral *Stmt) {
  StringBuilder Builder(IRModule, IRBuilder);
  LastInstr = Builder.BuildLiteral(Stmt->GetValue());
}

static TokenType ResolveAssignmentOperation(TokenType T) {
  switch (T) {
  case TOK_MUL_ASSIGN:
    return TOK_STAR;
  case TOK_DIV_ASSIGN:
    return TOK_SLASH;
  case TOK_MOD_ASSIGN:
    return TOK_MOD;
  case TOK_PLUS_ASSIGN:
    return TOK_PLUS;
  case TOK_MINUS_ASSIGN:
    return TOK_MINUS;
  case TOK_SHL_ASSIGN:
    return TOK_SHL;
  case TOK_SHR_ASSIGN:
    return TOK_SHR;
  case TOK_BIT_AND_ASSIGN:
    return TOK_BIT_AND;
  case TOK_BIT_OR_ASSIGN:
    return TOK_BIT_OR;
  case TOK_XOR_ASSIGN:
    return TOK_XOR;
  default:
    weak::UnreachablePoint("Should not reach here");
  }
}

void CodeGen::Visit(const ASTBinaryOperator *Stmt) {
  Stmt->GetLHS()->Accept(this);
  llvm::Value *L = LastInstr;
  /// This is needed only in case of assignment to array element.
  llvm::Value *AssignmentArrayPtr = LastArrayPtr;
  Stmt->GetRHS()->Accept(this);
  llvm::Value *R = LastInstr;

  if (!L || !R)
    return;

  weak::AssertSame(Stmt, L, R);

  ScalarExprEmitter ScalarEmitter(IRCtx, IRBuilder);

  switch (auto T = Stmt->GetOperation()) {
  case TOK_ASSIGN: {
    AssignmentIRBuilder Builder(IRBuilder, DeclStorage);
    Builder.Build(Stmt, R, AssignmentArrayPtr);
    LastArrayPtr = nullptr;
    break;
  }
  case TOK_MUL_ASSIGN:
  case TOK_DIV_ASSIGN:
  case TOK_PLUS_ASSIGN:
  case TOK_MINUS_ASSIGN:
  case TOK_MOD_ASSIGN:
  case TOK_SHL_ASSIGN:
  case TOK_SHR_ASSIGN:
  case TOK_BIT_AND_ASSIGN:
  case TOK_BIT_OR_ASSIGN:
  case TOK_XOR_ASSIGN: {
    auto *Assignment = static_cast<const ASTSymbol *>(Stmt->GetLHS());
    llvm::AllocaInst *Variable = DeclStorage.Lookup(Assignment->GetName());
    TokenType Op = ResolveAssignmentOperation(T);
    LastInstr = ScalarEmitter.EmitBinOp(Stmt, Op, L, R);
    IRBuilder.CreateStore(LastInstr, Variable);
    break;
  }
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
  case TOK_BIT_OR:
  case TOK_BIT_AND:
  case TOK_XOR:
  case TOK_SHL:
  case TOK_SHR:
    LastInstr = ScalarEmitter.EmitBinOp(Stmt, T, L, R);
    break;
  default: {
    LastInstr = nullptr;

    weak::UnreachablePoint(
        "Should not reach here. Operators are checked by parser.");
    break;
  }
  } // switch
}

void CodeGen::Visit(const ASTUnaryOperator *Stmt) {
  switch (Stmt->GetOperand()->GetASTType()) {
  case AST_SYMBOL:
  case AST_ARRAY_ACCESS:
    break;
  default:
    weak::CompileError(Stmt)
        << "Variable as argument of unary operator expected";
  }

  Stmt->GetOperand()->Accept(this);

  llvm::Value *Step = IRBuilder.getInt32(1);

  const auto *SymbolOperand =
      static_cast<const ASTSymbol *>(Stmt->GetOperand());

  switch (Stmt->GetOperation()) {
  case TOK_INC:
    LastInstr = IRBuilder.CreateAdd(LastInstr, Step);
    break;
  case TOK_DEC:
    LastInstr = IRBuilder.CreateSub(LastInstr, Step);
    break;
  default:
    weak::UnreachablePoint("Should not reach here");
  } // switch

  IRBuilder.CreateStore(LastInstr,
                        DeclStorage.Lookup(SymbolOperand->GetName()));
}

void CodeGen::Visit(const ASTForStmt *Stmt) {
  DeclStorage.StartScope();
  /// \todo: Generate code with respect to empty for parameters,
  ///        e.g for (;;), or for(int i = 0; ; ++i). Also
  ///        break,continue statements should be implemented.
  Stmt->GetInit()->Accept(this);

  llvm::Function *Func = IRBuilder.GetInsertBlock()->getParent();

  llvm::BasicBlock *ForCondBB =
      llvm::BasicBlock::Create(IRCtx, "for.cond", Func);
  llvm::BasicBlock *ForBodyBB =
      llvm::BasicBlock::Create(IRCtx, "for.body", Func);
  llvm::BasicBlock *ForEndBB = llvm::BasicBlock::Create(IRCtx, "for.end", Func);

  IRBuilder.CreateBr(ForCondBB);
  IRBuilder.SetInsertPoint(ForCondBB);

  Stmt->GetCondition()->Accept(this);
  IRBuilder.CreateCondBr(LastInstr, ForBodyBB, ForEndBB);
  IRBuilder.SetInsertPoint(ForBodyBB);
  Stmt->GetBody()->Accept(this);
  Stmt->GetIncrement()->Accept(this);
  IRBuilder.CreateBr(ForCondBB);
  IRBuilder.SetInsertPoint(ForEndBB);

  DeclStorage.EndScope();
}

void CodeGen::Visit(const ASTWhileStmt *Stmt) {
  llvm::Function *Func = IRBuilder.GetInsertBlock()->getParent();

  llvm::BasicBlock *WhileCondBB =
      llvm::BasicBlock::Create(IRCtx, "while.cond", Func);
  llvm::BasicBlock *WhileBodyBB =
      llvm::BasicBlock::Create(IRCtx, "while.body", Func);
  llvm::BasicBlock *WhileEndBB =
      llvm::BasicBlock::Create(IRCtx, "while.end", Func);

  IRBuilder.CreateBr(WhileCondBB);
  IRBuilder.SetInsertPoint(WhileCondBB);

  Stmt->GetCondition()->Accept(this);
  IRBuilder.CreateCondBr(LastInstr, WhileBodyBB, WhileEndBB);
  IRBuilder.SetInsertPoint(WhileBodyBB);
  Stmt->GetBody()->Accept(this);
  IRBuilder.CreateBr(WhileCondBB);
  IRBuilder.SetInsertPoint(WhileEndBB);
}

void CodeGen::Visit(const ASTDoWhileStmt *Stmt) {
  llvm::Function *Func = IRBuilder.GetInsertBlock()->getParent();

  llvm::BasicBlock *DoWhileBodyBB =
      llvm::BasicBlock::Create(IRCtx, "do.while.body", Func);
  llvm::BasicBlock *DoWhileEndBB =
      llvm::BasicBlock::Create(IRCtx, "do.while.end", Func);

  IRBuilder.CreateBr(DoWhileBodyBB);
  IRBuilder.SetInsertPoint(DoWhileBodyBB);

  Stmt->GetBody()->Accept(this);
  Stmt->GetCondition()->Accept(this);
  IRBuilder.CreateCondBr(LastInstr, DoWhileBodyBB, DoWhileEndBB);
  IRBuilder.SetInsertPoint(DoWhileEndBB);
}

void CodeGen::Visit(const ASTIfStmt *Stmt) {
  Stmt->GetCondition()->Accept(this);
  llvm::Value *Condition = LastInstr;

  /// \todo: I am not sure if we should always compare with 0.
  unsigned NumBits = Condition->getType()->getPrimitiveSizeInBits();
  Condition = IRBuilder.CreateICmpNE(Condition, IRBuilder.getIntN(NumBits, 0));

  llvm::Function *Func = IRBuilder.GetInsertBlock()->getParent();

  auto *ThenBB = llvm::BasicBlock::Create(IRCtx, "if.then", Func);
  auto *ElseBB = llvm::BasicBlock::Create(IRCtx, "if.else");
  auto *MergeBB = llvm::BasicBlock::Create(IRCtx, "if.end");

  if (Stmt->GetElseBody())
    IRBuilder.CreateCondBr(Condition, ThenBB, ElseBB);
  else
    IRBuilder.CreateCondBr(Condition, ThenBB, MergeBB);

  IRBuilder.SetInsertPoint(ThenBB);
  Stmt->GetThenBody()->Accept(this);
  IRBuilder.CreateBr(MergeBB);

  if (!Stmt->GetElseBody()) {
    Func->getBasicBlockList().push_back(MergeBB);
    IRBuilder.SetInsertPoint(MergeBB);
    return;
  }

  Func->getBasicBlockList().push_back(ElseBB);
  IRBuilder.SetInsertPoint(ElseBB);

  Stmt->GetElseBody()->Accept(this);
  IRBuilder.CreateBr(MergeBB);

  Func->getBasicBlockList().push_back(MergeBB);
  IRBuilder.SetInsertPoint(MergeBB);
}

void CodeGen::Visit(const ASTFunctionDecl *Decl) {
  FunctionBuilder FunctionBuilder(IRCtx, IRModule, Decl);

  llvm::Function *Func = FunctionBuilder.BuildSignature();
  llvm::BasicBlock *CFGBlock = llvm::BasicBlock::Create(IRCtx, "entry", Func);
  IRBuilder.SetInsertPoint(CFGBlock);

  DeclStorage.StartScope();

  for (auto &Arg : Func->args()) {
    auto *ArgAlloca = IRBuilder.CreateAlloca(Arg.getType());
    IRBuilder.CreateStore(&Arg, ArgAlloca);
    DeclStorage.Push(Arg.getName().str(), ArgAlloca);
  }

  Decl->GetBody()->Accept(this);
  DeclStorage.EndScope();
  llvm::verifyFunction(*Func);
  LastInstr = nullptr;

  if (Decl->GetReturnType() == TOK_VOID)
    IRBuilder.CreateRetVoid();
}

void CodeGen::Visit(const ASTFunctionCall *Stmt) {
  llvm::Function *Callee = IRModule.getFunction(Stmt->GetName());
  if (!Callee)
    weak::CompileError(Stmt)
        << "Function `" << Stmt->GetName() << "` not found";

  const auto &FunArgs = Stmt->GetArguments();

  if (Callee->arg_size() != FunArgs.size())
    weak::CompileError(Stmt)
        << "Arguments size mismatch: " << FunArgs.size() << " got, but "
        << Callee->arg_size() << " expected";

  llvm::SmallVector<llvm::Value *, 16> Args;
  for (size_t I = 0; I < FunArgs.size(); ++I) {
    auto *AST = FunArgs[I];

    AST->Accept(this);

    auto *InstrType = LastInstr->getType();
    auto *ExpectedType = Callee->getArg(I)->getType();

    weak::AssertSame(AST, InstrType, ExpectedType);

    Args.push_back(LastInstr);
  }

  LastInstr = IRBuilder.CreateCall(Callee, Args);
}

void CodeGen::Visit(const ASTFunctionPrototype *Stmt) {
  FunctionBuilder FunctionBuilder(IRCtx, IRModule, Stmt);
  FunctionBuilder.BuildSignature();
}

void CodeGen::Visit(const ASTArrayAccess *Stmt) {
  llvm::AllocaInst *SymbolValue = DeclStorage.Lookup(Stmt->GetSymbolName());
  if (!SymbolValue)
    weak::CompileError(Stmt)
        << "Variable `" << Stmt->GetSymbolName() << "` not found";

  LastInstr =
      IRBuilder.CreateLoad(SymbolValue->getAllocatedType(), SymbolValue);

  llvm::Value *Array = LastInstr;
  Stmt->GetIndex()->Accept(this);
  llvm::Value *Index = LastInstr;

  if (Index->getType() != llvm::Type::getInt32Ty(IRCtx))
    weak::CompileError(Stmt) << "Expected 32-bit integer as array index";

  weak::AssertNotOutOfRange(Stmt, SymbolValue, Index);
  /// If you have a question about this, please see
  /// https://llvm.org/docs/GetElementPtr.html.
  llvm::Value *Zero = IRBuilder.getInt32(0);

  // \todo: Unary operators with values accesses through [] does not works.
  if (Array->getType()->isPointerTy())
    /// Pointer.
    LastArrayPtr = IRBuilder.CreateInBoundsGEP(
        Array->getType()->getPointerElementType(), Array, Index);
  else
    /// Array.
    LastArrayPtr = IRBuilder.CreateInBoundsGEP(
        Array->getType(), llvm::getPointerOperand(Array), {Zero, Index});

  LastInstr = IRBuilder.CreateLoad(
      LastArrayPtr->getType()->getPointerElementType(), LastArrayPtr);
}

void CodeGen::Visit(const ASTSymbol *Stmt) {
  llvm::AllocaInst *SymbolValue = DeclStorage.Lookup(Stmt->GetName());
  if (!SymbolValue)
    weak::CompileError(Stmt)
        << "Variable `" << Stmt->GetName() << "` not found";

  if (SymbolValue->getAllocatedType()->isArrayTy()) {
    llvm::Value *Zero = IRBuilder.getInt32(0);
    LastInstr = IRBuilder.CreateInBoundsGEP(SymbolValue->getAllocatedType(),
                                            SymbolValue, {Zero, Zero});
  } else
    LastInstr =
        IRBuilder.CreateLoad(SymbolValue->getAllocatedType(), SymbolValue);
}

void CodeGen::Visit(const ASTCompoundStmt *Stmts) {
  DeclStorage.StartScope();
  for (const auto &Stmt : Stmts->GetStmts())
    Stmt->Accept(this);
  DeclStorage.EndScope();
}

void CodeGen::Visit(const ASTReturnStmt *Stmt) {
  llvm::Function *Func = IRBuilder.GetInsertBlock()->getParent();

  if (Func->getReturnType()->isVoidTy())
    weak::CompileError(Stmt) << "Cannot return value from void function";

  Stmt->GetOperand()->Accept(this);
  IRBuilder.CreateRet(LastInstr);
}

void CodeGen::Visit(const ASTArrayDecl *Stmt) {
  TypeResolver TypeResolver(IRCtx);

  llvm::Type *UnderlyingType = TypeResolver.Resolve(Stmt->GetDataType());
  /// \todo: Temporarily we get only first dimension as parameter and don't
  ///        do something else.
  llvm::AllocaInst *ArrayDecl = IRBuilder.CreateAlloca(
      llvm::ArrayType::get(UnderlyingType, Stmt->GetArityList()[0]));

  DeclStorage.Push(Stmt->GetSymbolName(), ArrayDecl);
}

void CodeGen::Visit(const ASTVarDecl *Decl) {
  if (DeclStorage.Lookup(Decl->GetSymbolName()))
    weak::CompileError(Decl)
        << "Variable `" << Decl->GetSymbolName() << "` already declared";

  Decl->GetDeclBody()->Accept(this);

  llvm::Value *LiteralValue = LastInstr;

  /// Special case, since we need to copy array from data section to another
  /// array, placed on stack.
  if (Decl->GetDataType() == TOK_STRING) {
    const auto *Literal = static_cast<ASTStringLiteral *>(Decl->GetDeclBody());
    const unsigned NullTerminator = 1;
    llvm::ArrayType *ArrayType = llvm::ArrayType::get(
        IRBuilder.getInt8Ty(), Literal->GetValue().size() + NullTerminator);
    llvm::AllocaInst *Mem = IRBuilder.CreateAlloca(ArrayType);
    llvm::Value *CastedPtr =
        IRBuilder.CreateBitCast(Mem, IRBuilder.getInt8PtrTy());
    IRBuilder.CreateMemCpy(
        /*Dst=*/CastedPtr,
        /*DstAlign=*/llvm::MaybeAlign(1),
        /*Src=*/LiteralValue,
        /*SrcAlign=*/llvm::MaybeAlign(1),
        /*Size=*/ArrayType->getNumElements(),
        /*isVolatile=*/false);
    DeclStorage.Push(Decl->GetSymbolName(), Mem);
    return;
  }

  TypeResolver TypeResolver(IRCtx);
  llvm::AllocaInst *VarDecl = IRBuilder.CreateAlloca(
      TypeResolver.ResolveExceptVoid(Decl->GetDataType()));
  IRBuilder.CreateStore(LastInstr, VarDecl);
  DeclStorage.Push(Decl->GetSymbolName(), VarDecl);
}

llvm::Module &CodeGen::GetModule() { return IRModule; }

const llvm::SymbolTableList<llvm::GlobalVariable> &
CodeGen::GetGlobalVariables() const {
  return IRModule.getGlobalList();
}

const llvm::SymbolTableList<llvm::Function> &
CodeGen::GetGlobalFunctions() const {
  return IRModule.getFunctionList();
}

std::string CodeGen::ToString() const {
  std::string Result;

  for (const auto &Global : GetGlobalVariables()) {
    llvm::raw_string_ostream Stream(Result);
    Stream << Global;
    Stream << '\n';
    Stream.flush();
  }

  Result += '\n';

  for (const auto &F : GetGlobalFunctions()) {
    llvm::raw_string_ostream Stream(Result);
    Stream << F;
    Stream << '\n';
    Stream.flush();
  }

  return Result;
}

} // namespace weak