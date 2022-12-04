/* CodeGen.cpp - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/CodeGen.h"

#include "FrontEnd/AST/AST.h"
#include "MiddleEnd/CodeGen/ScalarExprEmitter.h"
#include "MiddleEnd/CodeGen/TypeResolver.h"
#include "Utility/Unreachable.h"
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
template <typename ASTFunctionDeclOrPrototype>
class FunctionBuilder {
public:
  FunctionBuilder(
    llvm::IRBuilder<>          &I,
    llvm::Module               &M,
    ASTFunctionDeclOrPrototype *Decl
  ) : mIRBuilder(I)
    , mIRModule(M)
    , mDecl(Decl)
    , mResolver(mIRBuilder) {}

  llvm::Function *BuildSignature() {
    /// \todo: Always external linkage? Come here after making multiple files
    ///        compilation.
    return llvm::Function::Create(
      CreateSignature(),
      llvm::Function::ExternalLinkage,
      mDecl->Name(),
      &mIRModule
    );
  }

private:
  llvm::FunctionType *CreateSignature() {
    llvm::SmallVector<llvm::Type *, 16> ArgTypes;

    for (const auto &ArgAST : mDecl->Args())
      ArgTypes.push_back(ResolveParamType(ArgAST));

    return llvm::FunctionType::get(
      /* Return type.         */mResolver.Resolve(mDecl->ReturnType()),
      /* Arguments.           */std::move(ArgTypes),
      /* Variadic parameters? */false
    );
  }

  llvm::Type *ResolveParamType(ASTNode *AST) {
    if (AST->Is(AST_VAR_DECL))
      return mResolver.ResolveExceptVoid(
        static_cast<ASTVarDecl *>(AST)->DataType()
      );

    return llvm::PointerType::get(
      mResolver.ResolveExceptVoid(
        static_cast<ASTArrayDecl *>(AST)->DataType()
      ),
      /*AddressSpace=*/0
    );
  }

  llvm::IRBuilder<> &mIRBuilder;
  llvm::Module &mIRModule;
  ASTFunctionDeclOrPrototype *mDecl;
  TypeResolver mResolver;
};

} // namespace
} // namespace weak

namespace weak {

CodeGen::CodeGen(ASTNode *Root)
  : mRoot(Root)
  , mLastInstr(nullptr)
  , mIRModule("LLVM Module", mIRCtx)
  , mIRBuilder(mIRCtx) {}

void CodeGen::CreateCode() {
  mRoot->Accept(this);
}

void CodeGen::Visit(ASTBool *Stmt) {
  mLastInstr = mIRBuilder.getInt1(Stmt->Value());
}

void CodeGen::Visit(ASTChar *Stmt) {
  mLastInstr = mIRBuilder.getInt8(Stmt->Value());
}

void CodeGen::Visit(ASTNumber *Stmt) {
  mLastInstr = mIRBuilder.getInt32(Stmt->Value());
}

void CodeGen::Visit(ASTFloat *Stmt) {
  llvm::APFloat Float(Stmt->Value());
  mLastInstr = llvm::ConstantFP::get(mIRCtx, Float);
}

void CodeGen::Visit(ASTString *Stmt) {
  auto *Literal = mIRBuilder.CreateGlobalString(Stmt->Value());
  Literal->setDSOLocal(false);
  mLastInstr = llvm::ConstantExpr::getBitCast(
    Literal,
    mIRBuilder.getInt8PtrTy()
  );
}

static TokenType ResolveAssignmentOp(TokenType T) {
  switch (T) {
  case TOK_MUL_ASSIGN:     return TOK_STAR;
  case TOK_DIV_ASSIGN:     return TOK_SLASH;
  case TOK_MOD_ASSIGN:     return TOK_MOD;
  case TOK_PLUS_ASSIGN:    return TOK_PLUS;
  case TOK_MINUS_ASSIGN:   return TOK_MINUS;
  case TOK_SHL_ASSIGN:     return TOK_SHL;
  case TOK_SHR_ASSIGN:     return TOK_SHR;
  case TOK_BIT_AND_ASSIGN: return TOK_BIT_AND;
  case TOK_BIT_OR_ASSIGN:  return TOK_BIT_OR;
  case TOK_XOR_ASSIGN:     return TOK_XOR;
  default:                 Unreachable("Should not reach there.");
  }
}

void CodeGen::Visit(ASTBinary *Stmt) {
  auto *LHS = Stmt->LHS();
  auto *RHS = Stmt->RHS();

  LHS->Accept(this);
  llvm::Value *L = mLastInstr;
  RHS->Accept(this);
  llvm::Value *R = mLastInstr;

  /// Load value and save pointer to it.
  llvm::Value *ArrayPtr{nullptr};
  if (LHS->Is(AST_ARRAY_ACCESS)) {
    ArrayPtr = L;
    L = mIRBuilder.CreateLoad(L->getType()->getPointerElementType(), L);
  }

  /// Load only value, since right hand side is never writeable.
  if (RHS->Is(AST_ARRAY_ACCESS))
    R = mIRBuilder.CreateLoad(R->getType()->getPointerElementType(), R);

  if (!L || !R)
    return;

  ScalarExprEmitter ScalarEmitter(mIRBuilder);

  switch (auto T = Stmt->Operation()) {
  case TOK_ASSIGN: {
    if (LHS->Is(AST_ARRAY_ACCESS))
      mIRBuilder.CreateStore(R, ArrayPtr);
    else if (LHS->Is(AST_MEMBER_ACCESS)) {
      auto *MA = static_cast<ASTMemberAccess *>(LHS);
      const auto &Name = MA->Name()->Name();
      auto *Type = llvm::StructType::getTypeByName(mIRCtx, mStructVarsStorage[Name]);

      llvm::AllocaInst *Struct = mStorage.Lookup(Name);
      /// \todo: Get AST for declaration and convert `.field` to index
      mLastInstr = mIRBuilder.CreateStructGEP(Type, Struct, 1);
      mIRBuilder.CreateStore(R, mLastInstr);
    } else {
      auto *Symbol = static_cast<ASTSymbol *>(LHS);
      llvm::AllocaInst *Variable = mStorage.Lookup(Symbol->Name());
      mIRBuilder.CreateStore(R, Variable);
    }
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
    auto *Symbol = static_cast<ASTSymbol *>(LHS);
    llvm::AllocaInst *Variable = mStorage.Lookup(Symbol->Name());
    TokenType Op = ResolveAssignmentOp(T);
    mLastInstr = ScalarEmitter.EmitBinOp(Op, L, R);
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
    mLastInstr = ScalarEmitter.EmitBinOp(T, L, R);
    break;
  default:
    Unreachable("Should not reach there.");
  }
}

static TokenType ResolveUnaryOp(TokenType T) {
  switch (T) {
  case TOK_INC: return TOK_PLUS;
  case TOK_DEC: return TOK_MINUS;
  default:      Unreachable("Should not reach there.");
  }
}

void CodeGen::Visit(ASTUnary *Stmt) {
  Stmt->Operand()->Accept(this);
  llvm::Value *Op = mLastInstr;
  llvm::Value *ArrayPtr{nullptr};

  if (Stmt->Operand()->Is(AST_ARRAY_ACCESS)) {
    ArrayPtr = Op;
    Op = mIRBuilder.CreateLoad(Op->getType()->getPointerElementType(), Op);
  }

  ScalarExprEmitter ScalarEmitter(mIRBuilder);

  switch (auto T = Stmt->Operation()) {
  case TOK_INC:
  case TOK_DEC:
    mLastInstr = ScalarEmitter.EmitBinOp(ResolveUnaryOp(T), Op, mIRBuilder.getInt32(1));
    break;
  default:
    Unreachable("Should not reach there.");
  }

  auto *Symbol = static_cast<ASTSymbol *>(Stmt->Operand());

  mIRBuilder.CreateStore(
    mLastInstr,
    ArrayPtr ? ArrayPtr : mStorage.Lookup(Symbol->Name())
  );
}

void CodeGen::Visit(ASTFor *Stmt) {
  mStorage.StartScope();

  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  if (auto *I = Stmt->Init())
    I->Accept(this);

  llvm::BasicBlock *CondBB{nullptr};

  auto *BodyBB = llvm::BasicBlock::Create(mIRCtx, "for.body", Func);
  auto *EndBB  = llvm::BasicBlock::Create(mIRCtx, "for.end", Func);

  if (auto *C = Stmt->Condition()) {
    CondBB = llvm::BasicBlock::Create(mIRCtx, "for.cond", Func);
    mIRBuilder.CreateBr(CondBB);
    mIRBuilder.SetInsertPoint(CondBB);
    C->Accept(this);
    mIRBuilder.CreateCondBr(mLastInstr, BodyBB, EndBB);
  } else
    mIRBuilder.CreateBr(BodyBB);

  mIRBuilder.SetInsertPoint(BodyBB);
  Stmt->Body()->Accept(this);

  if (auto *I = Stmt->Increment())
    I->Accept(this);

  mIRBuilder.CreateBr(CondBB ? CondBB : BodyBB);
  mIRBuilder.SetInsertPoint(EndBB);

  mStorage.EndScope();
}

void CodeGen::Visit(ASTWhile *Stmt) {
  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  auto *CondBB = llvm::BasicBlock::Create(mIRCtx, "while.cond", Func);
  auto *BodyBB = llvm::BasicBlock::Create(mIRCtx, "while.body", Func);
  auto *EndBB  = llvm::BasicBlock::Create(mIRCtx, "while.end", Func);

  mIRBuilder.CreateBr(CondBB);
  mIRBuilder.SetInsertPoint(CondBB);

  Stmt->Condition()->Accept(this);
  mIRBuilder.CreateCondBr(mLastInstr, BodyBB, EndBB);
  mIRBuilder.SetInsertPoint(BodyBB);
  Stmt->Body()->Accept(this);
  mIRBuilder.CreateBr(CondBB);
  mIRBuilder.SetInsertPoint(EndBB);
}

void CodeGen::Visit(ASTDoWhile *Stmt) {
  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  auto *BodyBB = llvm::BasicBlock::Create(mIRCtx, "do.while.body", Func);
  auto *EndBB  = llvm::BasicBlock::Create(mIRCtx, "do.while.end", Func);

  mIRBuilder.CreateBr(BodyBB);
  mIRBuilder.SetInsertPoint(BodyBB);

  Stmt->Body()->Accept(this);
  Stmt->Condition()->Accept(this);
  mIRBuilder.CreateCondBr(mLastInstr, BodyBB, EndBB);
  mIRBuilder.SetInsertPoint(EndBB);
}

void CodeGen::Visit(ASTIf *Stmt) {
  Stmt->Condition()->Accept(this);
  llvm::Value *Cond = mLastInstr;

  unsigned NumBits = Cond->getType()->getPrimitiveSizeInBits();
  Cond = mIRBuilder.CreateICmpNE(Cond, mIRBuilder.getIntN(NumBits, 0));

  llvm::Function *Func = mIRBuilder.GetInsertBlock()->getParent();

  auto *ThenBB  = llvm::BasicBlock::Create(mIRCtx, "if.then", Func);
  auto *ElseBB  = llvm::BasicBlock::Create(mIRCtx, "if.else");
  auto *MergeBB = llvm::BasicBlock::Create(mIRCtx, "if.end");

  mIRBuilder.CreateCondBr(Cond, ThenBB, Stmt->ElseBody() ? ElseBB : MergeBB);
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

const std::string &ASTDeclName(ASTNode *AST) {
  if (AST->Is(AST_VAR_DECL))
    return static_cast<ASTVarDecl *>(AST)->Name();

  if (AST->Is(AST_ARRAY_DECL))
    return static_cast<ASTArrayDecl *>(AST)->Name();

  Unreachable("Expected variable or array declaration.");
}

void CodeGen::Visit(ASTFunctionDecl *Decl) {
  FunctionBuilder B(mIRBuilder, mIRModule, Decl);
  llvm::Function *Func = B.BuildSignature();

  auto *EntryBB = llvm::BasicBlock::Create(mIRCtx, "entry", Func);
  mIRBuilder.SetInsertPoint(EntryBB);

  mStorage.StartScope();

  auto ASTArgIt = Decl->Args().begin();
  for (auto &Arg : Func->args()) {
    auto *ArgAlloca = mIRBuilder.CreateAlloca(Arg.getType());
    mIRBuilder.CreateStore(&Arg, ArgAlloca);
    mStorage.Push(ASTDeclName(*ASTArgIt++), ArgAlloca);
  }

  Decl->Body()->Accept(this);
  mStorage.EndScope();
  llvm::verifyFunction(*Func);
  mLastInstr = nullptr;

  if (Decl->ReturnType() == DT_VOID)
    mIRBuilder.CreateRetVoid();
}

void CodeGen::Visit(ASTFunctionCall *Stmt) {
  llvm::Function *Callee = mIRModule.getFunction(Stmt->Name());
  const auto &FunArgs = Stmt->Args();

  llvm::SmallVector<llvm::Value *, 16> Args;
  for (auto *Arg : FunArgs) {
    Arg->Accept(this);
    Args.push_back(mLastInstr);
  }

  mLastInstr = mIRBuilder.CreateCall(Callee, Args);
}

void CodeGen::Visit(ASTFunctionPrototype *Stmt) {
  FunctionBuilder B(mIRBuilder, mIRModule, Stmt);
  B.BuildSignature();
}

void CodeGen::Visit(ASTArrayAccess *Stmt) {
  llvm::AllocaInst *Symbol = mStorage.Lookup(Stmt->Name());
  llvm::Value *Array = mIRBuilder.CreateLoad(Symbol->getAllocatedType(), Symbol);
  Stmt->Index()->Accept(this);
  llvm::Value *Index = mLastInstr;

  /// If you have a question about this, please see
  /// https://llvm.org/docs/ElementPtr.html.
  llvm::Value *Zero = mIRBuilder.getInt32(0);

  if (Array->getType()->isPointerTy())
    /// Pointer.
    mLastInstr = mIRBuilder.CreateInBoundsGEP(
      Array->getType()->getPointerElementType(),
      Array,
      Index
    );
  else
    /// Array.
    mLastInstr = mIRBuilder.CreateInBoundsGEP(
      Array->getType(),
      llvm::getPointerOperand(Array),
      { Zero, Index }
    );
}

void CodeGen::Visit(ASTSymbol *Stmt) {
  llvm::AllocaInst *Symbol = mStorage.Lookup(Stmt->Name());
  llvm::Type *SymbolTy = Symbol->getAllocatedType();

  if (SymbolTy->isArrayTy())
    mLastInstr = mIRBuilder.CreateConstGEP2_32(SymbolTy, Symbol, 0, 0);
  else
    mLastInstr = mIRBuilder.CreateLoad(SymbolTy, Symbol);
}

void CodeGen::Visit(ASTCompound *Stmts) {
  mStorage.StartScope();
  for (ASTNode *Stmt : Stmts->Stmts())
    Stmt->Accept(this);
  mStorage.EndScope();
}

void CodeGen::Visit(ASTReturn *Stmt) {
  Stmt->Operand()->Accept(this);
  mIRBuilder.CreateRet(mLastInstr);
}

void CodeGen::Visit(ASTMemberAccess *Stmt) {
  const auto &Name = Stmt->Name()->Name();
  auto *Type = llvm::StructType::getTypeByName(mIRCtx, mStructVarsStorage[Name]);

  llvm::AllocaInst *Struct = mStorage.Lookup(Name);
  assert(Struct);
  /// \todo: Get AST for declaration and convert `.field` to index
  mLastInstr = mIRBuilder.CreateStructGEP(Type, Struct, 1);
  mLastInstr = mIRBuilder.CreateLoad(Type->getTypeAtIndex(1U), mLastInstr);
  /// \todo: Get type, with respect to nested member accesses.
}

void CodeGen::Visit(ASTArrayDecl *Stmt) {
  TypeResolver TR(mIRBuilder);
  llvm::Type *ArrayTy = TR.Resolve(Stmt);
  llvm::AllocaInst *ArrayDecl = mIRBuilder.CreateAlloca(ArrayTy);
  mStorage.Push(Stmt->Name(), ArrayDecl);
}

void CodeGen::Visit(ASTVarDecl *Decl) {
  auto *Body = Decl->Body();

  if (!Body && Decl->DataType() == DT_STRUCT) {
    mStructVarsStorage.emplace(Decl->Name(), Decl->TypeName());
    auto *VarDecl = mIRBuilder.CreateAlloca(
        llvm::StructType::getTypeByName(
          mIRCtx,
          Decl->TypeName()
        )
      );
    mStorage.Push(Decl->Name(), VarDecl);
    return;
  }

  Body->Accept(this);

  /// Special case, since we need to copy array from data section to another
  /// array, placed on stack.
  if (Decl->DataType() == DT_STRING) {
    llvm::Value *LiteralValue = mLastInstr;
    auto *Literal = static_cast<ASTString *>(Body);
    unsigned NullTerminator = 1;
    llvm::ArrayType *ArrayType = llvm::ArrayType::get(
      mIRBuilder.getInt8Ty(),
      Literal->Value().size() + NullTerminator
    );
    llvm::AllocaInst *Mem = mIRBuilder.CreateAlloca(ArrayType);
    llvm::Value *CastedPtr = mIRBuilder.CreateBitCast(Mem, mIRBuilder.getInt8PtrTy());
    mIRBuilder.CreateMemCpy(
      /*Dst=*/CastedPtr,
      /*DstAlign=*/llvm::MaybeAlign(1),
      /*Src=*/LiteralValue,
      /*SrcAlign=*/llvm::MaybeAlign(1),
      /*Size=*/ArrayType->getNumElements(),
      /*isVolatile=*/false
    );
    mStorage.Push(Decl->Name(), Mem);
    return;
  }

  TypeResolver TR(mIRBuilder);
  auto *VarDecl = mIRBuilder.CreateAlloca(TR.ResolveExceptVoid(Decl->DataType()));

  mIRBuilder.CreateStore(mLastInstr, VarDecl);
  mStorage.Push(Decl->Name(), VarDecl);
}

void CodeGen::Visit(ASTStructDecl *Decl) {
  auto *Struct = llvm::StructType::create(mIRCtx);
  Struct->setName(Decl->Name());
  llvm::SmallVector<llvm::Type *, 8> Members;

  TypeResolver TR(mIRBuilder);

  for (auto *D : Decl->Decls())
    Members.push_back(TR.Resolve(D));

  Struct->setBody(std::move(Members));

  mLastInstr = nullptr;
}

llvm::Module &CodeGen::Module() {
  return mIRModule;
}

const llvm::SymbolTableList<llvm::GlobalVariable> &CodeGen::GlobalVariables() const {
  return mIRModule.getGlobalList();
}

const llvm::SymbolTableList<llvm::Function> &CodeGen::GlobalFunctions() const {
  return mIRModule.getFunctionList();
}

std::vector<llvm::StructType *> CodeGen::Types() const {
  return mIRModule.getIdentifiedStructTypes();
}

std::string CodeGen::ToString() const {
  std::string Result;

  for (auto *T : Types())
    llvm::raw_string_ostream{Result} << *T << '\n';

  for (const auto &V : GlobalVariables())
    llvm::raw_string_ostream{Result} << V << '\n';

  if (!Result.empty())
    Result += '\n';

  for (const auto &F : GlobalFunctions())
    llvm::raw_string_ostream{Result} << F << '\n';

  return Result;
}

} // namespace weak