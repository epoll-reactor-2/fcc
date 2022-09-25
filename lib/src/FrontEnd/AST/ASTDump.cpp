/* ASTDump.cpp - helper function to dump AST to stdout.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTDump.hpp"
#include "FrontEnd/AST/ASTArrayAccess.hpp"
#include "FrontEnd/AST/ASTArrayDecl.hpp"
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
#include "FrontEnd/AST/ASTNode.hpp"
#include "FrontEnd/AST/ASTReturnStmt.hpp"
#include "FrontEnd/AST/ASTStringLiteral.hpp"
#include "FrontEnd/AST/ASTSymbol.hpp"
#include "FrontEnd/AST/ASTUnaryOperator.hpp"
#include "FrontEnd/AST/ASTVarDecl.hpp"
#include "FrontEnd/AST/ASTVisitor.hpp"
#include "FrontEnd/AST/ASTWhileStmt.hpp"
#include <iostream>

template <typename RAIt>
static std::string IntegerRangeToString(RAIt Begin, RAIt End) {
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

using namespace weak::frontEnd;

namespace {

class ASTDumpVisitor : public ASTVisitor {
public:
  ASTDumpVisitor(ASTNode *TheRootNode, std::ostream &TheOutStream)
      : RootNode(TheRootNode), Indent(0U), OutStream(TheOutStream) {}

  void Dump() { RootNode->Accept(this); }

private:
  void Visit(const ASTArrayAccess *Decl) override {
    PrintWithTextPosition("ArrayAccess", Decl, /*NewLineNeeded=*/false);

    OutStream << Decl->GetSymbolName() << std::endl;

    Indent += 2;
    PrintIndent();
    Decl->GetIndex()->Accept(this);
    Indent -= 2;
  }

  void Visit(const ASTArrayDecl *Decl) override {
    PrintWithTextPosition("ArrayDecl", Decl, /*NewLineNeeded=*/false);

    const auto &ArityList = Decl->GetArityList();
    OutStream << TokenToString(Decl->GetDataType()) << " "
              << IntegerRangeToString(ArityList.cbegin(), ArityList.cend())
              << " ";
    OutStream << Decl->GetSymbolName() << std::endl;
  }

  void Visit(const ASTBinaryOperator *Binary) override {
    PrintWithTextPosition("BinaryOperator", Binary, /*NewLineNeeded=*/false);
    OutStream << TokenToString(Binary->GetOperation()) << std::endl;
    Indent += 2;

    PrintIndent();
    Binary->GetLHS()->Accept(this);

    PrintIndent();
    Binary->GetRHS()->Accept(this);

    Indent -= 2;
  }

  void Visit(const ASTBooleanLiteral *Boolean) override {
    PrintWithTextPosition("BooleanLiteral", Boolean, /*NewLineNeeded=*/false);
    OutStream << std::boolalpha << Boolean->GetValue() << std::endl;
  }

  void Visit(const ASTBreakStmt *BreakStmt) override {
    PrintWithTextPosition("BreakStmt", BreakStmt, /*NewLineNeeded=*/true);
  }

  void Visit(const ASTCompoundStmt *CompoundStmt) override {
    PrintWithTextPosition("CompoundStmt", CompoundStmt, /*NewLineNeeded=*/true);

    Indent += 2;
    for (const auto &Stmt : CompoundStmt->GetStmts()) {
      PrintIndent();
      Stmt->Accept(this);
    }
    Indent -= 2;
  }

  void Visit(const ASTContinueStmt *ContinueStmt) override {
    PrintWithTextPosition("ContinueStmt", ContinueStmt, /*NewLineNeeded=*/true);
  }

  void Visit(const ASTFloatingPointLiteral *Float) override {
    PrintWithTextPosition("FloatingPointLiteral", Float,
                          /*NewLineNeeded=*/false);
    OutStream << Float->GetValue() << std::endl;
  }

  void Visit(const ASTForStmt *ForStmt) override {
    PrintWithTextPosition("ForStmt", ForStmt,
                          /*NewLineNeeded=*/true);

    Indent += 2;

    if (auto *Init = ForStmt->GetInit().get()) {
      PrintIndent();
      PrintWithTextPosition("ForStmtInit", Init,
                            /*NewLineNeeded=*/true);
      Indent += 2;
      PrintIndent();
      Init->Accept(this);
      Indent -= 2;
    }

    if (auto *Condition = ForStmt->GetCondition().get()) {
      PrintIndent();
      PrintWithTextPosition("ForStmtCondition", Condition,
                            /*NewLineNeeded=*/true);
      Indent += 2;
      PrintIndent();
      Condition->Accept(this);
      Indent -= 2;
    }

    if (auto *Increment = ForStmt->GetIncrement().get()) {
      PrintIndent();
      PrintWithTextPosition("ForStmtIncrement", Increment,
                            /*NewLineNeeded=*/true);
      Indent += 2;
      PrintIndent();
      Increment->Accept(this);
      Indent -= 2;
    }

    if (const auto *Body = ForStmt->GetBody().get()) {
      PrintIndent();
      PrintWithTextPosition("ForStmtBody", Body,
                            /*NewLineNeeded=*/true);
      Indent += 2;
      PrintIndent();
      Visit(Body);
      Indent -= 2;
    }

    Indent -= 2;
  }

  void Visit(const ASTIfStmt *IfStmt) override {
    PrintWithTextPosition("IfStmt", IfStmt, /*NewLineNeeded=*/true);
    Indent += 2;

    if (const auto &Condition = IfStmt->GetCondition()) {
      PrintIndent();
      PrintWithTextPosition("IfStmtCondition", Condition.get(),
                            /*NewLineNeeded=*/true);
      Indent += 2;
      PrintIndent();
      Condition->Accept(this);
      Indent -= 2;
    }

    if (const auto &ThenBody = IfStmt->GetThenBody()) {
      PrintIndent();
      PrintWithTextPosition("IfStmtThenBody", ThenBody.get(),
                            /*NewLineNeeded=*/true);
      Indent += 2;
      PrintIndent();
      Visit(ThenBody.get());
      Indent -= 2;
    }

    if (const auto &ElseBody = IfStmt->GetElseBody()) {
      PrintIndent();
      PrintWithTextPosition("IfStmtElseBody", ElseBody.get(),
                            /*NewLineNeeded=*/true);
      Indent += 2;
      PrintIndent();
      Visit(ElseBody.get());
      Indent -= 2;
    }
    Indent -= 2;
  }

  void Visit(const ASTIntegerLiteral *Integer) override {
    PrintWithTextPosition("IntegerLiteral", Integer,
                          /*NewLineNeeded=*/false);
    OutStream << Integer->GetValue() << std::endl;
  }

  void Visit(const ASTReturnStmt *ReturnStmt) override {
    PrintWithTextPosition("ReturnStmt", ReturnStmt, /*NewLineNeeded=*/true);
    Indent += 2;

    if (ReturnStmt->GetOperand()) {
      PrintIndent();
      ReturnStmt->GetOperand()->Accept(this);
    }

    Indent -= 2;
  }

  void Visit(const ASTStringLiteral *String) override {
    PrintWithTextPosition("StringLiteral", String,
                          /*NewLineNeeded=*/false);
    OutStream << String->GetValue() << std::endl;
  }

  void Visit(const ASTSymbol *Symbol) override {
    PrintWithTextPosition("Symbol", Symbol,
                          /*NewLineNeeded=*/false);
    OutStream << Symbol->GetName() << std::endl;
  }

  void Visit(const ASTUnaryOperator *Unary) override {
    OutStream << (Unary->PrefixOrPostfix == ASTUnaryOperator::UnaryType::PREFIX
                      ? "Prefix "
                      : "Postfix ");
    PrintWithTextPosition("UnaryOperator", Unary,
                          /*NewLineNeeded=*/false);
    OutStream << TokenToString(Unary->GetOperation()) << std::endl;
    Indent += 2;

    PrintIndent();
    Unary->GetOperand()->Accept(this);

    Indent -= 2;
  }

  void Visit(const ASTVarDecl *VarDecl) override {
    PrintWithTextPosition("VarDeclStmt", VarDecl, /*NewLineNeeded=*/false);
    OutStream << TokenToString(VarDecl->GetDataType()) << " "
              << VarDecl->GetSymbolName() << std::endl;

    if (const auto &Body = VarDecl->GetDeclareBody()) {
      Indent += 2;
      PrintIndent();
      Body->Accept(this);
      Indent -= 2;
    }
  }

  void Visit(const ASTFunctionDecl *FunctionDecl) override {
    PrintWithTextPosition("FunctionDecl", FunctionDecl, /*NewLineNeeded=*/true);

    Indent += 2;
    PrintIndent();
    PrintWithTextPosition("FunctionDeclRetType", FunctionDecl,
                          /*NewLineNeeded=*/false);
    OutStream << TokenToString(FunctionDecl->GetReturnType()) << std::endl;

    PrintIndent();
    PrintWithTextPosition("FunctionDeclName", FunctionDecl,
                          /*NewLineNeeded=*/false);
    OutStream << FunctionDecl->GetName() << std::endl;

    PrintIndent();
    PrintWithTextPosition("FunctionDeclArgs", FunctionDecl,
                          /*NewLineNeeded=*/true);

    Indent += 2;
    for (const auto &Argument : FunctionDecl->GetArguments()) {
      PrintIndent();
      Argument->Accept(this);
    }
    Indent -= 2;

    PrintIndent();
    PrintWithTextPosition("FunctionDeclBody", FunctionDecl,
                          /*NewLineNeeded=*/true);

    Indent += 2;
    PrintIndent();
    Visit(FunctionDecl->GetBody().get());
    Indent -= 2;
  }

  void Visit(const ASTFunctionCall *FunctionCall) override {
    PrintWithTextPosition("FunctionCall", FunctionCall,
                          /*NewLineNeeded=*/false);
    OutStream << FunctionCall->GetName() << std::endl;

    Indent += 2;
    PrintIndent();
    PrintWithTextPosition("FunctionCallArgs", FunctionCall,
                          /*NewLineNeeded=*/true);

    Indent += 2;
    for (const auto &Argument : FunctionCall->GetArguments()) {
      PrintIndent();
      Argument->Accept(this);
    }
    Indent -= 2;

    Indent -= 2;
  }

  void Visit(const ASTFunctionPrototype *FunctionPrototype) override {
    PrintWithTextPosition("FunctionPrototype", FunctionPrototype,
                          /*NewLineNeeded=*/false);
    OutStream << FunctionPrototype->GetName() << std::endl;

    Indent += 2;
    PrintIndent();
    PrintWithTextPosition("FunctionPrototypeArgs", FunctionPrototype,
                          /*NewLineNeeded=*/true);

    Indent += 2;
    for (const auto &Argument : FunctionPrototype->GetArguments()) {
      PrintIndent();
      Argument->Accept(this);
    }
    Indent -= 2;

    Indent -= 2;
  }

  void Visit(const ASTDoWhileStmt *DoWhileStmt) override {
    CommonWhileStmtVisit(DoWhileStmt, /*IsDoWhile=*/true);
  }

  void Visit(const ASTWhileStmt *WhileStmt) override {
    CommonWhileStmtVisit(WhileStmt, /*IsDoWhile=*/false);
  }

  template <typename WhileNode>
  void CommonWhileStmtVisit(const WhileNode *WhileStmt, bool IsDoWhile) {
    using namespace std::string_literals;
    PrintWithTextPosition((IsDoWhile ? "Do"s : ""s) + "WhileStmt", WhileStmt,
                          /*NewLineNeeded=*/true);

    auto PrintWhileCondition = [&] {
      if (const auto &Condition = WhileStmt->GetCondition().get()) {
        PrintIndent();
        PrintWithTextPosition((IsDoWhile ? "Do"s : ""s) + "WhileStmtCond",
                              Condition,
                              /*NewLineNeeded=*/true);
        Indent += 2;
        PrintIndent();
        Condition->Accept(this);
        Indent -= 2;
      }
    };

    auto PrintWhileBody = [&] {
      if (const auto &Body = WhileStmt->GetBody().get()) {
        PrintIndent();
        PrintWithTextPosition((IsDoWhile ? "Do"s : ""s) + "WhileStmtBody", Body,
                              /*NewLineNeeded=*/true);
        Indent += 2;
        PrintIndent();
        Visit(Body);
        Indent -= 2;
      }
    };

    Indent += 2;

    if (IsDoWhile) {
      PrintWhileBody();
      PrintWhileCondition();
    } else {
      PrintWhileCondition();
      PrintWhileBody();
    }

    Indent -= 2;
  }

  void PrintWithTextPosition(std::string_view Label, const ASTNode *Node,
                             bool NewLineNeeded) const {
    OutStream << Label << " <line:" << Node->GetLineNo()
              << ", col:" << Node->GetColumnNo() << ">";

    if (NewLineNeeded)
      OutStream << std::endl;
    else
      OutStream << " ";
  }

  void PrintIndent() const { OutStream << std::string(Indent, ' '); }

  ASTNode *RootNode;
  unsigned Indent;
  std::ostream &OutStream;
};

} // namespace

namespace weak {

void frontEnd::ASTDump(ASTNode *RootNode, std::ostream &OutStream) {
  ASTDumpVisitor DumpVisitor(RootNode, OutStream);
  DumpVisitor.Dump();
}

void frontEnd::ASTDump(const std::unique_ptr<ASTNode> &RootNode,
                       std::ostream &OutStream) {
  ASTDump(RootNode.get(), OutStream);
}

} // namespace weak