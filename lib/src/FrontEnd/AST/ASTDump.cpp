/* ASTDump.cpp - AST dumper.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTDump.h"
#include "FrontEnd/AST/AST.h"
#include "FrontEnd/AST/ASTVisitor.h"
#include "FrontEnd/Lex/Token.h"

template <typename It>
static std::string IntegerRangeToString(It Begin, It End) {
  std::string Output;
  Output.reserve(std::distance(Begin, End));

  Output += "[";
  for (; Begin != End; ++Begin)
    Output += std::to_string(*Begin) + "][";

  if (!Output.empty()) {
    Output.pop_back();
    Output.pop_back();
  }

  Output += "]";

  return Output;
}

namespace weak {
namespace {

class ASTDumpVisitor : public ASTVisitor {
public:
  ASTDumpVisitor(ASTNode *RootNode, std::ostream &Stream)
      : mRootNode(RootNode), mIndent(0U), mStream(Stream) {}

  void Dump() { mRootNode->Accept(this); }

private:
  void Visit(ASTArrayAccess *Decl) override {
    PrintWithTextPos("ArrayAccess", Decl, /*NewLineNeeded=*/false);

    mStream << Decl->Name() << std::endl;

    mIndent += 2;
    PrintIndent();
    Decl->Index()->Accept(this);
    mIndent -= 2;
  }

  void Visit(ASTArrayDecl *Decl) override {
    PrintWithTextPos("ArrayDecl", Decl, /*NewLineNeeded=*/false);

    const auto &ArityList = Decl->ArityList();
    mStream << TokenToString(Decl->DataType()) << " "
            << IntegerRangeToString(ArityList.cbegin(), ArityList.cend())
            << " ";
    mStream << Decl->Name() << std::endl;
  }

  void Visit(ASTBinary *Binary) override {
    PrintWithTextPos("BinaryOperator", Binary, /*NewLineNeeded=*/false);
    mStream << TokenToString(Binary->Operation()) << std::endl;
    mIndent += 2;

    PrintIndent();
    Binary->LHS()->Accept(this);

    PrintIndent();
    Binary->RHS()->Accept(this);

    mIndent -= 2;
  }

  void Visit(ASTBool *Boolean) override {
    PrintWithTextPos("BooleanLiteral", Boolean, /*NewLineNeeded=*/false);
    mStream << std::boolalpha << Boolean->Value() << std::endl;
  }

  void Visit(ASTBreak *BreakStmt) override {
    PrintWithTextPos("BreakStmt", BreakStmt, /*NewLineNeeded=*/true);
  }

  void Visit(ASTChar *Char) override {
    PrintWithTextPos("CharLiteral", Char, /*NewLineNeeded=*/false);
    mStream << "'" << Char->Value() << "'" << std::endl;
  }

  void Visit(ASTCompound *CompoundStmt) override {
    PrintWithTextPos("CompoundStmt", CompoundStmt, /*NewLineNeeded=*/true);

    mIndent += 2;
    for (const auto &Stmt : CompoundStmt->Stmts()) {
      PrintIndent();
      Stmt->Accept(this);
    }
    mIndent -= 2;
  }

  void Visit(ASTContinue *ContinueStmt) override {
    PrintWithTextPos("ContinueStmt", ContinueStmt, /*NewLineNeeded=*/true);
  }

  void Visit(ASTFloat *Float) override {
    PrintWithTextPos("FloatingPointLiteral", Float,
                     /*NewLineNeeded=*/false);
    mStream << Float->Value() << std::endl;
  }

  void Visit(ASTFor *ForStmt) override {
    PrintWithTextPos("ForStmt", ForStmt,
                     /*NewLineNeeded=*/true);

    mIndent += 2;

    if (auto *Init = ForStmt->Init()) {
      PrintIndent();
      PrintWithTextPos("ForStmtInit", Init,
                       /*NewLineNeeded=*/true);
      mIndent += 2;
      PrintIndent();
      Init->Accept(this);
      mIndent -= 2;
    }

    if (auto *Condition = ForStmt->Condition()) {
      PrintIndent();
      PrintWithTextPos("ForStmtCondition", Condition,
                       /*NewLineNeeded=*/true);
      mIndent += 2;
      PrintIndent();
      Condition->Accept(this);
      mIndent -= 2;
    }

    if (auto *Increment = ForStmt->Increment()) {
      PrintIndent();
      PrintWithTextPos("ForStmtIncrement", Increment,
                       /*NewLineNeeded=*/true);
      mIndent += 2;
      PrintIndent();
      Increment->Accept(this);
      mIndent -= 2;
    }

    if (auto *Body = ForStmt->Body()) {
      PrintIndent();
      PrintWithTextPos("ForStmtBody", Body,
                       /*NewLineNeeded=*/true);
      mIndent += 2;
      PrintIndent();
      Visit(Body);
      mIndent -= 2;
    }

    mIndent -= 2;
  }

  void Visit(ASTIf *IfStmt) override {
    PrintWithTextPos("IfStmt", IfStmt, /*NewLineNeeded=*/true);
    mIndent += 2;

    if (auto *Condition = IfStmt->Condition()) {
      PrintIndent();
      PrintWithTextPos("IfStmtCondition", Condition,
                       /*NewLineNeeded=*/true);
      mIndent += 2;
      PrintIndent();
      Condition->Accept(this);
      mIndent -= 2;
    }

    if (auto *ThenBody = IfStmt->ThenBody()) {
      PrintIndent();
      PrintWithTextPos("IfStmtThenBody", ThenBody,
                       /*NewLineNeeded=*/true);
      mIndent += 2;
      PrintIndent();
      Visit(ThenBody);
      mIndent -= 2;
    }

    if (auto *ElseBody = IfStmt->ElseBody()) {
      PrintIndent();
      PrintWithTextPos("IfStmtElseBody", ElseBody,
                       /*NewLineNeeded=*/true);
      mIndent += 2;
      PrintIndent();
      Visit(ElseBody);
      mIndent -= 2;
    }
    mIndent -= 2;
  }

  void Visit(ASTNumber *Integer) override {
    PrintWithTextPos("IntegerLiteral", Integer,
                     /*NewLineNeeded=*/false);
    mStream << Integer->Value() << std::endl;
  }

  void Visit(ASTReturn *ReturnStmt) override {
    PrintWithTextPos("ReturnStmt", ReturnStmt, /*NewLineNeeded=*/true);
    mIndent += 2;

    if (ReturnStmt->Operand()) {
      PrintIndent();
      ReturnStmt->Operand()->Accept(this);
    }

    mIndent -= 2;
  }

  void Visit(ASTString *String) override {
    PrintWithTextPos("StringLiteral", String,
                     /*NewLineNeeded=*/false);
    mStream << String->Value() << std::endl;
  }

  void Visit(ASTSymbol *Symbol) override {
    PrintWithTextPos("Symbol", Symbol,
                     /*NewLineNeeded=*/false);
    mStream << Symbol->Name() << std::endl;
  }

  void Visit(ASTUnary *Unary) override {
    mStream << (Unary->PrefixOrPostfix == ASTUnary::PREFIX ? "Prefix "
                                                           : "Postfix ");
    PrintWithTextPos("UnaryOperator", Unary,
                     /*NewLineNeeded=*/false);
    mStream << TokenToString(Unary->Operation()) << std::endl;
    mIndent += 2;

    PrintIndent();
    Unary->Operand()->Accept(this);

    mIndent -= 2;
  }

  void Visit(ASTStructDecl *Decl) override {
    PrintWithTextPos("StructDecl", Decl, /*NewLineNeeded=*/false);
    mStream << Decl->Name() << std::endl;

    mIndent += 2;
    for (const auto &Field : Decl->Decls()) {
      PrintIndent();
      Field->Accept(this);
    }
    mIndent -= 2;
  }

  void Visit(ASTVarDecl *VarDecl) override {
    PrintWithTextPos("VarDecl", VarDecl, /*NewLineNeeded=*/false);
    mStream << TokenToString(VarDecl->DataType()) << " " << VarDecl->Name()
            << std::endl;

    if (auto *Body = VarDecl->Body()) {
      mIndent += 2;
      PrintIndent();
      Body->Accept(this);
      mIndent -= 2;
    }
  }

  void Visit(ASTFunctionDecl *FunctionDecl) override {
    PrintWithTextPos("FunctionDecl", FunctionDecl, /*NewLineNeeded=*/true);

    mIndent += 2;
    PrintIndent();
    PrintWithTextPos("FunctionDeclRetType", FunctionDecl,
                     /*NewLineNeeded=*/false);
    mStream << TokenToString(FunctionDecl->ReturnType()) << std::endl;

    PrintIndent();
    PrintWithTextPos("FunctionDeclName", FunctionDecl,
                     /*NewLineNeeded=*/false);
    mStream << FunctionDecl->Name() << std::endl;

    PrintIndent();
    PrintWithTextPos("FunctionDeclArgs", FunctionDecl,
                     /*NewLineNeeded=*/true);

    mIndent += 2;
    for (const auto &Argument : FunctionDecl->Args()) {
      PrintIndent();
      Argument->Accept(this);
    }
    mIndent -= 2;

    PrintIndent();
    PrintWithTextPos("FunctionDeclBody", FunctionDecl,
                     /*NewLineNeeded=*/true);

    mIndent += 2;
    PrintIndent();
    Visit(FunctionDecl->Body());
    mIndent -= 2;
  }

  void Visit(ASTFunctionCall *FunctionCall) override {
    PrintWithTextPos("FunctionCall", FunctionCall,
                     /*NewLineNeeded=*/false);
    mStream << FunctionCall->Name() << std::endl;

    mIndent += 2;
    PrintIndent();
    PrintWithTextPos("FunctionCallArgs", FunctionCall,
                     /*NewLineNeeded=*/true);

    mIndent += 2;
    for (const auto &Argument : FunctionCall->Args()) {
      PrintIndent();
      Argument->Accept(this);
    }
    mIndent -= 2;

    mIndent -= 2;
  }

  void Visit(ASTFunctionPrototype *FunctionPrototype) override {
    PrintWithTextPos("FunctionPrototype", FunctionPrototype,
                     /*NewLineNeeded=*/false);
    mStream << FunctionPrototype->Name() << std::endl;

    mIndent += 2;
    PrintIndent();
    PrintWithTextPos("FunctionPrototypeArgs", FunctionPrototype,
                     /*NewLineNeeded=*/true);

    mIndent += 2;
    for (const auto &Argument : FunctionPrototype->Args()) {
      PrintIndent();
      Argument->Accept(this);
    }
    mIndent -= 2;

    mIndent -= 2;
  }

  void Visit(ASTDoWhile *DoWhileStmt) override {
    CommonWhileStmtVisit(DoWhileStmt, /*IsDoWhile=*/true);
  }

  void Visit(ASTWhile *WhileStmt) override {
    CommonWhileStmtVisit(WhileStmt, /*IsDoWhile=*/false);
  }

  template <typename WhileNode>
  void CommonWhileStmtVisit(WhileNode *WhileStmt, bool IsDoWhile) {
    using namespace std::string_literals;
    PrintWithTextPos((IsDoWhile ? "Do"s : ""s) + "WhileStmt", WhileStmt,
                     /*NewLineNeeded=*/true);

    auto PrintWhileCondition = [&] {
      if (auto *Condition = WhileStmt->Condition()) {
        PrintIndent();
        PrintWithTextPos((IsDoWhile ? "Do"s : ""s) + "WhileStmtCond", Condition,
                         /*NewLineNeeded=*/true);
        mIndent += 2;
        PrintIndent();
        Condition->Accept(this);
        mIndent -= 2;
      }
    };

    auto PrintWhileBody = [&] {
      if (auto *Body = WhileStmt->Body()) {
        PrintIndent();
        PrintWithTextPos((IsDoWhile ? "Do"s : ""s) + "WhileStmtBody", Body,
                         /*NewLineNeeded=*/true);
        mIndent += 2;
        PrintIndent();
        Visit(Body);
        mIndent -= 2;
      }
    };

    mIndent += 2;

    if (IsDoWhile) {
      PrintWhileBody();
      PrintWhileCondition();
    } else {
      PrintWhileCondition();
      PrintWhileBody();
    }

    mIndent -= 2;
  }

  void PrintWithTextPos(std::string_view Label, ASTNode *Node,
                        bool NewLineNeeded) const {
    mStream << Label << " <line:" << Node->LineNo()
            << ", col:" << Node->ColumnNo() << ">";

    if (NewLineNeeded)
      mStream << std::endl;
    else
      mStream << " ";
  }

  void PrintIndent() const { mStream << std::string(mIndent, ' '); }

  ASTNode *mRootNode;
  unsigned mIndent;
  std::ostream &mStream;
};

} // namespace
} // namespace weak

void weak::ASTDump(ASTNode *RootNode, std::ostream &OutStream) {
  ASTDumpVisitor DumpVisitor(RootNode, OutStream);
  DumpVisitor.Dump();
}