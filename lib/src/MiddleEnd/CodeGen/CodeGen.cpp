/* CodeGen.cpp - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/CodeGen.h"

#include "FrontEnd/AST/AST.h"
#include "MiddleEnd/CodeGen/ScalarExprEmitter.h"
#include "MiddleEnd/CodeGen/TypeCheck.h"
#include "MiddleEnd/CodeGen/TypeResolver.h"
#include "Utility/Diagnostic.h"
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
  FunctionBuilder(llvm::IRBuilder<> &I, llvm::Module &M,
                  const ASTFunctionDeclOrPrototype *Decl)
      : mIRBuilder(I), mIRModule(M), mDecl(Decl) {}

  llvm::Function *BuildSignature() {
    llvm::FunctionType *Signature = CreateSignature();
    /// \todo: Always external linkage? Come here after making multiple files
    ///        compilation.
    llvm::Function *Func = llvm::Function::Create(
        Signature, llvm::Function::ExternalLinkage, mDecl->Name(), &mIRModule);

    unsigned Idx{0U};
    for (llvm::Argument &Arg : Func->args())
      Arg.setName(ExtractSymbol(mDecl->Arguments()[Idx++]));

    return Func;
  }

private:
  llvm::FunctionType *CreateSignature() {
    TypeResolver TypeResolver(mIRBuilder);
    llvm::SmallVector<llvm::Type *, 16> ArgTypes;

    for (const auto &ArgAST : mDecl->Arguments())
      ArgTypes.push_back(ResolveParamType(ArgAST));

    llvm::FunctionType *Signature = llvm::FunctionType::get(
        /// Return type.
        TypeResolver.Resolve(mDecl->ReturnType(), mDecl->LineNo(),
                             mDecl->ColumnNo()),
        /// Arguments.
        ArgTypes,
        /// Variadic parameters?
        false);

    return Signature;
  }

  llvm::Type *ResolveParamType(const ASTNode *ArgAST) {
    AssertDeclaration(ArgAST);

    TypeResolver TypeResolver(mIRBuilder);
    if (ArgAST->Is(AST_VAR_DECL))
      /// Variable.
      return TypeResolver.ResolveExceptVoid(ArgAST);

    /// Array.
    const auto *ArrayDecl = static_cast<const ASTArrayDecl *>(ArgAST);
    llvm::Type *UnderlyingType = TypeResolver.ResolveExceptVoid(
        ArrayDecl->DataType(), /*LocationAST=*/ArgAST);

    return llvm::PointerType::get(UnderlyingType, /*AddressSpace=*/0);
  }

  const std::string &ExtractSymbol(const ASTNode *Node) {
    AssertDeclaration(Node);
    const auto *VarDecl = static_cast<const ASTVarDecl *>(Node);
    return VarDecl->Name();
  }

  void AssertDeclaration(const ASTNode *Node) {
    if (!Node->Is(AST_VAR_DECL) && !Node->Is(AST_ARRAY_DECL))
      weak::UnreachablePoint("wrong AST nodes passed as function parameters");
  }

  llvm::IRBuilder<> &mIRBuilder;
  llvm::Module &mIRModule;
  const ASTFunctionDeclOrPrototype *mDecl;
};

} // namespace
} // namespace weak

namespace weak {
namespace {

/// Create string literal (actually an array of 8-bit integers).
class StringBuilder {
public:
  StringBuilder(llvm::Module &M, llvm::IRBuilder<> &I)
      : mIRModule(M), mIRBuilder(I) {}

  llvm::Constant *BuildLiteral(std::string_view Data) {
    llvm::Constant *DataArray = CreateDataArray(Data);

    llvm::GlobalVariable *GlobalVar = new llvm::GlobalVariable(
        mIRModule, DataArray->getType(), true,
        llvm::GlobalVariable::ExternalLinkage, DataArray);

    return llvm::ConstantExpr::getBitCast(
        GlobalVar, mIRBuilder.getInt8Ty()->getPointerTo());
  }

private:
  llvm::Constant *CreateDataArray(std::string_view Data) {
    llvm::SmallVector<llvm::Constant *> Chars;
    Chars.reserve(Data.size());

    for (char C : Data)
      Chars.push_back(mIRBuilder.getInt8(C));

    /// Since we are working with libc, we are expecting, that all strings
    /// will be ended with '\0'.
    Chars.push_back(CreateNullTerminator());

    size_t ArraySize = Chars.size();
    llvm::Constant *Array = llvm::ConstantArray::get(
        llvm::ArrayType::get(mIRBuilder.getInt8Ty(), ArraySize),
        std::move(Chars));

    return Array;
  }

  llvm::Constant *CreateNullTerminator() { return mIRBuilder.getInt8('\0'); }

  llvm::Module &mIRModule;
  llvm::IRBuilder<> &mIRBuilder;
};

} // namespace

namespace {

class AssignmentIRBuilder {
public:
  AssignmentIRBuilder(llvm::IRBuilder<> &I, const DeclsStorage &S)
      : mIRBuilder(I), mStorage(S) {}

  void Build(const ASTBinaryOperator *Stmt, llvm::Value *RHS,
             llvm::Value *ArrayPtr) {
    auto *LHS = Stmt->LHS();

    if (LHS->Is(AST_ARRAY_ACCESS))
      BuildArrayAssignment(RHS, ArrayPtr);
    else
      BuildRegularAssignment(LHS, RHS);
  }

private:
  void BuildArrayAssignment(llvm::Value *RHS, llvm::Value *ArrayPtr) {
    mIRBuilder.CreateStore(RHS, ArrayPtr);
  }

  void BuildRegularAssignment(const ASTNode *LHS, llvm::Value *RHS) {
    const auto *Symbol = static_cast<const ASTSymbol *>(LHS);
    llvm::AllocaInst *Variable = mStorage.Lookup(Symbol->Name());
    mIRBuilder.CreateStore(RHS, Variable);
  }

  llvm::IRBuilder<> &mIRBuilder;
  const DeclsStorage &mStorage;
};

} // namespace

CodeGen::CodeGen(ASTNode *TheRoot)
    : mRoot(TheRoot), mStorage(), mLastInstr(nullptr), mIRCtx(),
      mIRModule("LLVM Module", mIRCtx), mIRBuilder(mIRCtx) {}

void CodeGen::CreateCode() { mRoot->Accept(this); }

void CodeGen::Visit(const ASTBooleanLiteral *Stmt) {
  mLastInstr = mIRBuilder.getInt1(Stmt->Value());
}

void CodeGen::Visit(const ASTCharLiteral *Stmt) {
  mLastInstr = mIRBuilder.getInt8(Stmt->Value());
}

void CodeGen::Visit(const ASTIntegerLiteral *Stmt) {
  mLastInstr = mIRBuilder.getInt32(Stmt->Value());
}

void CodeGen::Visit(const ASTFloatingPointLiteral *Stmt) {
  llvm::APFloat Float(Stmt->Value());
  mLastInstr = llvm::ConstantFP::get(mIRCtx, Float);
}

void CodeGen::Visit(const ASTStringLiteral *Stmt) {
  StringBuilder Builder(mIRModule, mIRBuilder);
  mLastInstr = Builder.BuildLiteral(Stmt->Value());
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
  Stmt->LHS()->Accept(this);
  llvm::Value *L = mLastInstr;
  Stmt->RHS()->Accept(this);
  llvm::Value *R = mLastInstr;

  /// Load value and save pointer to it.
  llvm::Value *ArrayPtr{nullptr};
  if (Stmt->LHS()->Is(AST_ARRAY_ACCESS)) {
    ArrayPtr = L;
    L = mIRBuilder.CreateLoad(L->getType()->getPointerElementType(), L);
  }

  /// Load only value, since right hand side is never writeable.
  if (Stmt->RHS()->Is(AST_ARRAY_ACCESS))
    R = mIRBuilder.CreateLoad(R->getType()->getPointerElementType(), R);

  if (!L || !R)
    return;

  weak::AssertSame(Stmt, L, R);

  ScalarExprEmitter ScalarEmitter(mIRCtx, mIRBuilder);

  switch (auto T = Stmt->Operation()) {
  case TOK_ASSIGN: {
    AssignmentIRBuilder Builder(mIRBuilder, mStorage);
    Builder.Build(Stmt, R, ArrayPtr);
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
    auto *Assignment = static_cast<const ASTSymbol *>(Stmt->LHS());
    llvm::AllocaInst *Variable = mStorage.Lookup(Assignment->Name());
    TokenType Op = ResolveAssignmentOperation(T);
    mLastInstr = ScalarEmitter.EmitBinOp(Stmt, Op, L, R);
    mIRBuilder.CreateStore(mLastInstr, Variable);
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
    mLastInstr = ScalarEmitter.EmitBinOp(Stmt, T, L, R);
    break;
  default: {
    mLastInstr = nullptr;

    weak::UnreachablePoint(
        "Should not reach here. Operators are checked by parser.");
    break;
  }
  } // switch
}

void CodeGen::Visit(const ASTUnaryOperator *Stmt) {
  switch (Stmt->Operand()->Type()) {
  case AST_SYMBOL:
  case AST_ARRAY_ACCESS:
    break;
  default:
    weak::CompileError(Stmt)
        << "Variable as argument of unary operator expected";
  }

  Stmt->Operand()->Accept(this);

  llvm::Value *Step = mIRBuilder.getInt32(1);

  const auto *SymbolOperand = static_cast<const ASTSymbol *>(Stmt->Operand());

  switch (Stmt->Operation()) {
  case TOK_INC:
    mLastInstr = mIRBuilder.CreateAdd(mLastInstr, Step);
    break;
  case TOK_DEC:
    mLastInstr = mIRBuilder.CreateSub(mLastInstr, Step);
    break;
  default:
    weak::UnreachablePoint("Should not reach here");
  } // switch

  mIRBuilder.CreateStore(mLastInstr, mStorage.Lookup(SymbolOperand->Name()));
}

void CodeGen::Visit(const ASTForStmt *Stmt) {
  mStorage.StartScope();
  /// \todo: Generate code with respect to empty for parameters,
  ///        e.g for (;;), or for(int i = 0; ; ++i). Also
  ///        break,continue statements should be implemented.
  Stmt->Init()->Accept(this);

  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  auto *ForCondBB = llvm::BasicBlock::Create(mIRCtx, "for.cond", Func);
  auto *ForBodyBB = llvm::BasicBlock::Create(mIRCtx, "for.body", Func);
  auto *ForEndBB = llvm::BasicBlock::Create(mIRCtx, "for.end", Func);

  mIRBuilder.CreateBr(ForCondBB);
  mIRBuilder.SetInsertPoint(ForCondBB);

  Stmt->Condition()->Accept(this);
  mIRBuilder.CreateCondBr(mLastInstr, ForBodyBB, ForEndBB);
  mIRBuilder.SetInsertPoint(ForBodyBB);
  Stmt->Body()->Accept(this);
  Stmt->Increment()->Accept(this);
  mIRBuilder.CreateBr(ForCondBB);
  mIRBuilder.SetInsertPoint(ForEndBB);

  mStorage.EndScope();
}

void CodeGen::Visit(const ASTWhileStmt *Stmt) {
  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  auto *WhileCondBB = llvm::BasicBlock::Create(mIRCtx, "while.cond", Func);
  auto *WhileBodyBB = llvm::BasicBlock::Create(mIRCtx, "while.body", Func);
  auto *WhileEndBB = llvm::BasicBlock::Create(mIRCtx, "while.end", Func);

  mIRBuilder.CreateBr(WhileCondBB);
  mIRBuilder.SetInsertPoint(WhileCondBB);

  Stmt->Condition()->Accept(this);
  mIRBuilder.CreateCondBr(mLastInstr, WhileBodyBB, WhileEndBB);
  mIRBuilder.SetInsertPoint(WhileBodyBB);
  Stmt->Body()->Accept(this);
  mIRBuilder.CreateBr(WhileCondBB);
  mIRBuilder.SetInsertPoint(WhileEndBB);
}

void CodeGen::Visit(const ASTDoWhileStmt *Stmt) {
  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  auto *DoWhileBodyBB = llvm::BasicBlock::Create(mIRCtx, "do.while.body", Func);
  auto *DoWhileEndBB = llvm::BasicBlock::Create(mIRCtx, "do.while.end", Func);

  mIRBuilder.CreateBr(DoWhileBodyBB);
  mIRBuilder.SetInsertPoint(DoWhileBodyBB);

  Stmt->Body()->Accept(this);
  Stmt->Condition()->Accept(this);
  mIRBuilder.CreateCondBr(mLastInstr, DoWhileBodyBB, DoWhileEndBB);
  mIRBuilder.SetInsertPoint(DoWhileEndBB);
}

void CodeGen::Visit(const ASTIfStmt *Stmt) {
  Stmt->Condition()->Accept(this);
  llvm::Value *Condition = mLastInstr;

  /// \todo: I am not sure if we should always compare with 0.
  unsigned NumBits = Condition->getType()->getPrimitiveSizeInBits();
  Condition =
      mIRBuilder.CreateICmpNE(Condition, mIRBuilder.getIntN(NumBits, 0));

  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  auto *ThenBB = llvm::BasicBlock::Create(mIRCtx, "if.then", Func);
  auto *ElseBB = llvm::BasicBlock::Create(mIRCtx, "if.else");
  auto *MergeBB = llvm::BasicBlock::Create(mIRCtx, "if.end");

  if (Stmt->ElseBody())
    mIRBuilder.CreateCondBr(Condition, ThenBB, ElseBB);
  else
    mIRBuilder.CreateCondBr(Condition, ThenBB, MergeBB);

  mIRBuilder.SetInsertPoint(ThenBB);
  Stmt->ThenBody()->Accept(this);
  mIRBuilder.CreateBr(MergeBB);

  if (!Stmt->ElseBody()) {
    Func->getBasicBlockList().push_back(MergeBB);
    mIRBuilder.SetInsertPoint(MergeBB);
    return;
  }

  Func->getBasicBlockList().push_back(ElseBB);
  mIRBuilder.SetInsertPoint(ElseBB);

  Stmt->ElseBody()->Accept(this);
  mIRBuilder.CreateBr(MergeBB);

  Func->getBasicBlockList().push_back(MergeBB);
  mIRBuilder.SetInsertPoint(MergeBB);
}

void CodeGen::Visit(const ASTFunctionDecl *Decl) {
  FunctionBuilder FunctionBuilder(mIRBuilder, mIRModule, Decl);

  llvm::Function *Func = FunctionBuilder.BuildSignature();
  auto *CFGBlock = llvm::BasicBlock::Create(mIRCtx, "entry", Func);
  mIRBuilder.SetInsertPoint(CFGBlock);

  mStorage.StartScope();

  for (auto &Arg : Func->args()) {
    auto *ArgAlloca = mIRBuilder.CreateAlloca(Arg.getType());
    mIRBuilder.CreateStore(&Arg, ArgAlloca);
    mStorage.Push(Arg.getName().str(), ArgAlloca);
  }

  Decl->Body()->Accept(this);
  mStorage.EndScope();
  llvm::verifyFunction(*Func);
  mLastInstr = nullptr;

  if (Decl->ReturnType() == TOK_VOID)
    mIRBuilder.CreateRetVoid();
}

void CodeGen::Visit(const ASTFunctionCall *Stmt) {
  llvm::Function *Callee = mIRModule.getFunction(Stmt->Name());
  if (!Callee)
    weak::CompileError(Stmt) << "Function `" << Stmt->Name() << "` not found";

  const auto &FunArgs = Stmt->Arguments();

  if (Callee->arg_size() != FunArgs.size())
    weak::CompileError(Stmt)
        << "Arguments size mismatch: " << FunArgs.size() << " got, but "
        << Callee->arg_size() << " expected";

  llvm::SmallVector<llvm::Value *, 16> Args;
  for (size_t I = 0; I < FunArgs.size(); ++I) {
    auto *AST = FunArgs[I];

    AST->Accept(this);

    auto *InstrType = mLastInstr->getType();
    auto *ExpectedType = Callee->getArg(I)->getType();

    weak::AssertSame(AST, InstrType, ExpectedType);

    Args.push_back(mLastInstr);
  }

  mLastInstr = mIRBuilder.CreateCall(Callee, Args);
}

void CodeGen::Visit(const ASTFunctionPrototype *Stmt) {
  FunctionBuilder FunctionBuilder(mIRBuilder, mIRModule, Stmt);
  FunctionBuilder.BuildSignature();
}

void CodeGen::Visit(const ASTArrayAccess *Stmt) {
  llvm::AllocaInst *Symbol = mStorage.Lookup(Stmt->SymbolName());
  if (!Symbol)
    weak::CompileError(Stmt)
        << "Variable `" << Stmt->SymbolName() << "` not found";

  llvm::Value *Array =
      mIRBuilder.CreateLoad(Symbol->getAllocatedType(), Symbol);
  Stmt->Index()->Accept(this);
  llvm::Value *Index = mLastInstr;

  if (Index->getType() != mIRBuilder.getInt32Ty())
    weak::CompileError(Stmt) << "Expected 32-bit integer as array index";

  weak::AssertNotOutOfRange(Stmt, Symbol, Index);
  /// If you have a question about this, please see
  /// https://llvm.org/docs/ElementPtr.html.
  llvm::Value *Zero = mIRBuilder.getInt32(0);

  // \todo: Unary operators with values accesses through [] does not works.
  if (Array->getType()->isPointerTy())
    /// Pointer.
    mLastInstr = mIRBuilder.CreateInBoundsGEP(
        Array->getType()->getPointerElementType(), Array, Index);
  else
    /// Array.
    mLastInstr = mIRBuilder.CreateInBoundsGEP(
        Array->getType(), llvm::getPointerOperand(Array), {Zero, Index});
}

void CodeGen::Visit(const ASTSymbol *Stmt) {
  llvm::AllocaInst *SymbolValue = mStorage.Lookup(Stmt->Name());
  if (!SymbolValue)
    weak::CompileError(Stmt) << "Variable `" << Stmt->Name() << "` not found";

  if (SymbolValue->getAllocatedType()->isArrayTy()) {
    llvm::Value *Zero = mIRBuilder.getInt32(0);
    mLastInstr = mIRBuilder.CreateInBoundsGEP(SymbolValue->getAllocatedType(),
                                              SymbolValue, {Zero, Zero});
  } else
    mLastInstr =
        mIRBuilder.CreateLoad(SymbolValue->getAllocatedType(), SymbolValue);
}

void CodeGen::Visit(const ASTCompoundStmt *Stmts) {
  mStorage.StartScope();
  for (const auto &Stmt : Stmts->Stmts())
    Stmt->Accept(this);
  mStorage.EndScope();
}

void CodeGen::Visit(const ASTReturnStmt *Stmt) {
  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  if (Func->getReturnType()->isVoidTy())
    weak::CompileError(Stmt) << "Cannot return value from void function";

  Stmt->Operand()->Accept(this);
  mIRBuilder.CreateRet(mLastInstr);
}

void CodeGen::Visit(const ASTArrayDecl *Stmt) {
  TypeResolver TypeResolver(mIRBuilder);

  llvm::Type *UnderlyingType =
      TypeResolver.Resolve(Stmt->DataType(), /*LocationAST=*/Stmt);
  /// \todo: Temporarily we get only first dimension as parameter and don't
  ///        do something else.
  llvm::AllocaInst *ArrayDecl = mIRBuilder.CreateAlloca(
      llvm::ArrayType::get(UnderlyingType, Stmt->ArityList()[0]));

  mStorage.Push(Stmt->SymbolName(), ArrayDecl);
}

void CodeGen::Visit(const ASTVarDecl *Decl) {
  if (mStorage.Lookup(Decl->Name()))
    weak::CompileError(Decl)
        << "Variable `" << Decl->Name() << "` already declared";

  Decl->Body()->Accept(this);

  llvm::Value *LiteralValue = mLastInstr;

  /// Special case, since we need to copy array from data section to another
  /// array, placed on stack.
  if (Decl->DataType() == TOK_STRING) {
    const auto *Literal = static_cast<ASTStringLiteral *>(Decl->Body());
    const unsigned NullTerminator = 1;
    llvm::ArrayType *ArrayType = llvm::ArrayType::get(
        mIRBuilder.getInt8Ty(), Literal->Value().size() + NullTerminator);
    llvm::AllocaInst *Mem = mIRBuilder.CreateAlloca(ArrayType);
    llvm::Value *CastedPtr =
        mIRBuilder.CreateBitCast(Mem, mIRBuilder.getInt8PtrTy());
    mIRBuilder.CreateMemCpy(
        /*Dst=*/CastedPtr,
        /*DstAlign=*/llvm::MaybeAlign(1),
        /*Src=*/LiteralValue,
        /*SrcAlign=*/llvm::MaybeAlign(1),
        /*Size=*/ArrayType->getNumElements(),
        /*isVolatile=*/false);
    mStorage.Push(Decl->Name(), Mem);
    return;
  }

  TypeResolver TypeResolver(mIRBuilder);
  llvm::AllocaInst *VarDecl = mIRBuilder.CreateAlloca(
      TypeResolver.ResolveExceptVoid(Decl->DataType(), /*LocationAST=*/Decl));

  mIRBuilder.CreateStore(mLastInstr, VarDecl);
  mStorage.Push(Decl->Name(), VarDecl);
}

llvm::Module &CodeGen::Module() { return mIRModule; }

const llvm::SymbolTableList<llvm::GlobalVariable> &
CodeGen::GlobalVariables() const {
  return mIRModule.getGlobalList();
}

const llvm::SymbolTableList<llvm::Function> &CodeGen::GlobalFunctions() const {
  return mIRModule.getFunctionList();
}

std::string CodeGen::ToString() const {
  std::string Result;

  for (const auto &Global : GlobalVariables()) {
    llvm::raw_string_ostream Stream(Result);
    Stream << Global;
    Stream << '\n';
    Stream.flush();
  }

  Result += '\n';

  for (const auto &F : GlobalFunctions()) {
    llvm::raw_string_ostream Stream(Result);
    Stream << F;
    Stream << '\n';
    Stream.flush();
  }

  return Result;
}

} // namespace weak