/* CodeGen.cpp - LLVM IR generator.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/CodeGen/CodeGen.hpp"

#include "FrontEnd/AST/ASTBinaryOperator.hpp"
#include "FrontEnd/AST/ASTBooleanLiteral.hpp"
#include "FrontEnd/AST/ASTBreakStmt.hpp"
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

namespace {

/// Create part (without body and return type) of function IR from AST.
template <typename ASTFunctionDeclOrPrototype> class FunctionBuilder {
public:
  FunctionBuilder(llvm::LLVMContext &TheCtx, llvm::Module &TheModule,
                  const ASTFunctionDeclOrPrototype *TheDecl)
      : Ctx(TheCtx), Module(TheModule), Decl(TheDecl) {}

  llvm::Function *Build() {
    llvm::FunctionType *Signature = CreateSignature();
    llvm::Function *Func = llvm::Function::Create(
        Signature, llvm::Function::ExternalLinkage, Decl->GetName(), &Module);

    unsigned Idx{0U};
    for (llvm::Argument &Arg : Func->args())
      Arg.setName(ExtractSymbol(Decl->GetArguments()[Idx++].get()));

    return Func;
  }

private:
  llvm::FunctionType *CreateSignature() {
    weak::middleEnd::TypeResolver TypeResolver(Ctx);
    llvm::SmallVector<llvm::Type *, 16> ArgTypes;

    for (const auto &Arg : Decl->GetArguments())
      ArgTypes.push_back(TypeResolver.ResolveExceptVoid(Arg.get()));

    llvm::FunctionType *Signature = llvm::FunctionType::get(
        /// Return type.
        TypeResolver.Resolve(Decl->GetReturnType()),
        /// Arguments.
        ArgTypes,
        /// Variadic parameters?
        false);

    return Signature;
  }

  static const std::string &ExtractSymbol(const weak::frontEnd::ASTNode *Node) {
    const auto *VarDecl = static_cast<const weak::frontEnd::ASTVarDecl *>(Node);
    return VarDecl->GetSymbolName();
  }

  llvm::LLVMContext &Ctx;
  llvm::Module &Module;
  const ASTFunctionDeclOrPrototype *Decl;
};

} // namespace

namespace {

/// Create string literal (actually an array of 8-bit integers).
class StringLiteralBuilder {
public:
  StringLiteralBuilder(llvm::LLVMContext &TheCtx, llvm::Module &TheModule)
      : Ctx(TheCtx), Module(TheModule) {}

  llvm::Constant *Build(std::string_view Data) {
    llvm::Constant *DataArray = CreateDataArray(Data);

    llvm::GlobalVariable *GlobalVar = new llvm::GlobalVariable(
        Module, DataArray->getType(), true,
        llvm::GlobalVariable::ExternalLinkage, DataArray);

    return llvm::ConstantExpr::getBitCast(
        GlobalVar, llvm::Type::getInt8Ty(Ctx)->getPointerTo());
  }

private:
  llvm::Constant *CreateDataArray(std::string_view Data) {
    std::vector<llvm::Constant *> Chars;
    Chars.reserve(Data.size());

    for (char C : Data) {
      auto *CharConstantPtr =
          llvm::ConstantInt::get(llvm::Type::getInt8Ty(Ctx), C);
      Chars.push_back(CharConstantPtr);
    }
    /// Since we are working with libc, we are expecting, that all strings
    /// will be ended with '\0'.
    Chars.push_back(CreateNullTerminator());

    llvm::Constant *DataArray = llvm::ConstantArray::get(
        llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), Chars.size()), Chars);

    return DataArray;
  }

  llvm::Constant *CreateNullTerminator() {
    return llvm::ConstantInt::get(llvm::Type::getInt8Ty(Ctx), 0);
  }

  llvm::LLVMContext &Ctx;
  llvm::Module &Module;
};

} // namespace

namespace {

// Create temporary alloca instruction. Used to generate function parameters.
class TemporaryAllocaBuilder {
public:
  TemporaryAllocaBuilder(llvm::Function *TheFunc)
      : Func(TheFunc),
        CodeBuilder(&Func->getEntryBlock(), Func->getEntryBlock().begin()) {}

  llvm::AllocaInst *Build(llvm::Type *Type, std::string_view Name) {
    llvm::AllocaInst *Alloca = CodeBuilder.CreateAlloca(Type, nullptr, Name);
    return Alloca;
  }

private:
  llvm::Function *Func;
  llvm::IRBuilder<> CodeBuilder;
};

} // namespace

namespace weak {
namespace middleEnd {

CodeGen::CodeGen(frontEnd::ASTNode *TheRoot)
    : Root(TheRoot), DeclStorage(), LastInstr(nullptr), IRCtx(),
      IRModule("LLVM Module", IRCtx), IRBuilder(IRCtx) {}

void CodeGen::CreateCode() { Root->Accept(this); }

void CodeGen::Visit(const frontEnd::ASTBooleanLiteral *Stmt) {
  llvm::APInt Int(/*numBits=*/1, Stmt->GetValue(), false);
  LastInstr = llvm::ConstantInt::get(IRCtx, Int);
}

void CodeGen::Visit(const frontEnd::ASTIntegerLiteral *Stmt) {
  llvm::APInt Int(/*numBits=*/32, Stmt->GetValue(), false);
  LastInstr = llvm::ConstantInt::get(IRCtx, Int);
}

void CodeGen::Visit(const frontEnd::ASTFloatingPointLiteral *Stmt) {
  llvm::APFloat Float(Stmt->GetValue());
  LastInstr = llvm::ConstantFP::get(IRCtx, Float);
}

void CodeGen::Visit(const frontEnd::ASTStringLiteral *Stmt) {
  StringLiteralBuilder Builder(IRCtx, IRModule);
  LastInstr = Builder.Build(Stmt->GetValue());
}

static frontEnd::TokenType ResolveAssignmentOperation(frontEnd::TokenType T) {
  using frontEnd::TokenType;
  switch (T) {
  case TokenType::MUL_ASSIGN:
    return TokenType::STAR;
  case TokenType::DIV_ASSIGN:
    return TokenType::SLASH;
  case TokenType::MOD_ASSIGN:
    return TokenType::MOD;
  case TokenType::PLUS_ASSIGN:
    return TokenType::PLUS;
  case TokenType::MINUS_ASSIGN:
    return TokenType::MINUS;
  case TokenType::SHL_ASSIGN:
    return TokenType::SHL;
  case TokenType::SHR_ASSIGN:
    return TokenType::SHR;
  case TokenType::BIT_AND_ASSIGN:
    return TokenType::BIT_AND;
  case TokenType::BIT_OR_ASSIGN:
    return TokenType::BIT_OR;
  case TokenType::XOR_ASSIGN:
    return TokenType::XOR;
  default:
    weak::UnreachablePoint("Should not reach here");
  }
}

void CodeGen::Visit(const frontEnd::ASTBinaryOperator *Stmt) {
  Stmt->GetLHS()->Accept(this);
  llvm::Value *L = LastInstr;
  Stmt->GetRHS()->Accept(this);
  llvm::Value *R = LastInstr;

  if (!L || !R)
    return;

  weak::middleEnd::AssertSame(Stmt, L, R);

  ScalarExprEmitter ScalarEmitter(IRCtx, IRBuilder);

  using frontEnd::TokenType;
  switch (auto T = Stmt->GetOperation()) {
  case TokenType::ASSIGN: {
    const auto *Assignment =
        static_cast<const frontEnd::ASTSymbol *>(Stmt->GetLHS().get());
    llvm::AllocaInst *Variable = DeclStorage.Lookup(Assignment->GetName());
    IRBuilder.CreateStore(R, Variable);
    break;
  }
  case TokenType::MUL_ASSIGN:
  case TokenType::DIV_ASSIGN:
  case TokenType::PLUS_ASSIGN:
  case TokenType::MINUS_ASSIGN:
  case TokenType::MOD_ASSIGN:
  case TokenType::SHL_ASSIGN:
  case TokenType::SHR_ASSIGN:
  case TokenType::BIT_AND_ASSIGN:
  case TokenType::BIT_OR_ASSIGN:
  case TokenType::XOR_ASSIGN: {
    auto *Assignment =
        static_cast<const frontEnd::ASTSymbol *>(Stmt->GetLHS().get());
    llvm::AllocaInst *Variable = DeclStorage.Lookup(Assignment->GetName());
    TokenType Op = ResolveAssignmentOperation(T);
    LastInstr = ScalarEmitter.EmitBinOp(Stmt, Op, L, R);
    IRBuilder.CreateStore(LastInstr, Variable);
    break;
  }
  case TokenType::PLUS:
  case TokenType::MINUS:
  case TokenType::STAR:
  case TokenType::SLASH:
  case TokenType::LE:
  case TokenType::LT:
  case TokenType::GE:
  case TokenType::GT:
  case TokenType::EQ:
  case TokenType::NEQ:
  case TokenType::OR:
  case TokenType::AND:
  case TokenType::BIT_OR:
  case TokenType::BIT_AND:
  case TokenType::XOR:
  case TokenType::SHL:
  case TokenType::SHR:
    LastInstr = ScalarEmitter.EmitBinOp(Stmt, T, L, R);
    break;
  default: {
    LastInstr = nullptr;

    weak::CompileError(Stmt)
        << "Invalid binary operator: " << frontEnd::TokenToString(T);
    break;
  }
  } // switch
}

void CodeGen::Visit(const frontEnd::ASTUnaryOperator *Stmt) {
  Stmt->GetOperand()->Accept(this);

  llvm::APInt Int(32, 1, false);
  llvm::Value *Step = llvm::ConstantInt::get(IRCtx, Int);

  if (Stmt->GetOperand()->GetASTType() != frontEnd::ASTType::SYMBOL) {
    weak::CompileError(Stmt)
        << "Variable as argument of unary operator expected";
    return;
  }

  auto *SymbolOperand =
      static_cast<const frontEnd::ASTSymbol *>(Stmt->GetOperand().get());

  using frontEnd::TokenType;
  switch (Stmt->GetOperation()) {
  case TokenType::INC: {
    LastInstr = IRBuilder.CreateAdd(LastInstr, Step);
    // If we're expecting that unary operand is a variable,
    // the store operation was performed, when variable was
    // created or assigned, so we can safely do store.
    IRBuilder.CreateStore(LastInstr,
                          DeclStorage.Lookup(SymbolOperand->GetName()));
    break;
  }
  case TokenType::DEC: {
    LastInstr = IRBuilder.CreateSub(LastInstr, Step);
    IRBuilder.CreateStore(LastInstr,
                          DeclStorage.Lookup(SymbolOperand->GetName()));
    break;
  }
  default: {
    weak::CompileError(Stmt) << "Unknown unary operator";
    break;
  }
  } // switch
}

void CodeGen::Visit(const frontEnd::ASTForStmt *Stmt) {
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

void CodeGen::Visit(const frontEnd::ASTWhileStmt *Stmt) {
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

void CodeGen::Visit(const frontEnd::ASTDoWhileStmt *Stmt) {
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

void CodeGen::Visit(const frontEnd::ASTIfStmt *Stmt) {
  Stmt->GetCondition()->Accept(this);
  llvm::Value *Condition = LastInstr;

  /// \todo: I am not sure if we should always compare with 0.
  unsigned numBits = Condition->getType()->getPrimitiveSizeInBits();
  Condition = IRBuilder.CreateICmpNE(
      Condition, llvm::ConstantInt::get(IRCtx, llvm::APInt(numBits, 0, false)),
      "condition");

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

void CodeGen::Visit(const frontEnd::ASTFunctionDecl *Decl) {
  FunctionBuilder FunctionBuilder(IRCtx, IRModule, Decl);

  llvm::Function *Func = FunctionBuilder.Build();
  llvm::BasicBlock *CFGBlock = llvm::BasicBlock::Create(IRCtx, "entry", Func);
  IRBuilder.SetInsertPoint(CFGBlock);

  TemporaryAllocaBuilder AllocaBuilder(Func);

  DeclStorage.StartScope();

  for (auto &Arg : Func->args()) {
    llvm::AllocaInst *Alloca =
        AllocaBuilder.Build(Arg.getType(), Arg.getName().str());
    IRBuilder.CreateStore(&Arg, Alloca);
    DeclStorage.Push(Arg.getName().str(), Alloca);
  }

  Decl->GetBody()->Accept(this);
  DeclStorage.EndScope();
  llvm::verifyFunction(*Func);
  LastInstr = nullptr;
}

void CodeGen::Visit(const frontEnd::ASTFunctionCall *Stmt) {
  llvm::Function *Callee = IRModule.getFunction(Stmt->GetName());
  if (!Callee) {
    weak::CompileError(Stmt)
        << "Function `" << Stmt->GetName() << "` not found";
    return;
  }

  const auto &FunArgs = Stmt->GetArguments();

  if (Callee->arg_size() != FunArgs.size()) {
    weak::CompileError(Stmt)
        << "Arguments size mismatch: " << FunArgs.size() << " got, but "
        << Callee->arg_size() << " expected";
    return;
  }

  llvm::SmallVector<llvm::Value *, 16> Args;
  for (size_t I = 0; I < FunArgs.size(); ++I) {
    auto *AST = FunArgs[I].get();

    AST->Accept(this);

    auto *InstrType = LastInstr->getType();
    auto *ExpectedType = Callee->getArg(I)->getType();

    weak::middleEnd::AssertSame(AST, InstrType, ExpectedType);

    Args.push_back(LastInstr);
  }

  LastInstr = IRBuilder.CreateCall(Callee, Args);
}

void CodeGen::Visit(const frontEnd::ASTFunctionPrototype *Stmt) {
  FunctionBuilder FunctionBuilder(IRCtx, IRModule, Stmt);
  FunctionBuilder.Build();
}

void CodeGen::Visit(const frontEnd::ASTSymbol *Stmt) {
  llvm::Value *V = DeclStorage.Lookup(Stmt->GetName());
  if (!V) {
    weak::CompileError(Stmt)
        << "Variable `" << Stmt->GetName() << "` not found";
    return;
  }

  llvm::AllocaInst *Alloca = llvm::dyn_cast<llvm::AllocaInst>(V);
  if (Alloca)
    // Variable.
    LastInstr = IRBuilder.CreateLoad(Alloca->getAllocatedType(), Alloca,
                                     Stmt->GetName());
  else
    // Function parameter.
    LastInstr = V;
}

void CodeGen::Visit(const frontEnd::ASTCompoundStmt *Stmts) {
  DeclStorage.StartScope();
  for (const auto &Stmt : Stmts->GetStmts())
    Stmt->Accept(this);
  DeclStorage.EndScope();
}

void CodeGen::Visit(const frontEnd::ASTReturnStmt *Stmt) {
  llvm::Function *Func = IRBuilder.GetInsertBlock()->getParent();

  if (Func->getReturnType()->isVoidTy()) {
    weak::CompileError(Stmt) << "Cannot return value from void function";
    weak::UnreachablePoint();
  }

  Stmt->GetOperand()->Accept(this);
  IRBuilder.CreateRet(LastInstr);
}

void CodeGen::Visit(const frontEnd::ASTVarDecl *Decl) {
  Decl->GetDeclareBody()->Accept(this);

  /// Alloca needed to be able to store mutable variables.
  /// We should also do load and store before and after
  /// every use of Alloca variable.
  if (llvm::AllocaInst *Variable = DeclStorage.Lookup(Decl->GetSymbolName())) {
    IRBuilder.CreateStore(LastInstr, Variable);
  } else {
    TypeResolver TypeResolver(IRCtx);
    llvm::AllocaInst *Alloca = IRBuilder.CreateAlloca(
        TypeResolver.ResolveExceptVoid(Decl->GetDataType()), nullptr,
        Decl->GetSymbolName());
    IRBuilder.CreateStore(LastInstr, Alloca);
    DeclStorage.Push(Decl->GetSymbolName(), Alloca);
  }
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

} // namespace middleEnd
} // namespace weak