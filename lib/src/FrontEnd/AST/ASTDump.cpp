/* ASTDump.cpp - AST dumper.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "FrontEnd/AST/ASTDump.h"
#include "FrontEnd/AST/AST.h"
#include "FrontEnd/AST/ASTVisitor.h"
#include "Utility/EnumOstreamOperators.h"

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

  void Dump() {
    mRootNode->Accept(this);
  }

private:
  void Visit(ASTArrayAccess *Stmt) override {
    ASTTypePrint("ArrayAccess", Stmt);
    mStream << Stmt->Name() << '\n';

    mIndent += 2;
    for (auto *I : Stmt->Indices()) {
      PrintIndent();
      I->Accept(this);
    }
    mIndent -= 2;
  }

  void Visit(ASTArrayDecl *Decl) override {
    ASTTypePrint("ArrayDecl", Decl);

    const auto &ArityList = Decl->ArityList();
    mStream << Decl->DataType() << " "
            << IntegerRangeToString(ArityList.cbegin(), ArityList.cend())
            << " `";
    mStream << Decl->Name() << "`\n";
  }

  void Visit(ASTBinary *Stmt) override {
    ASTTypePrint("BinaryOperator", Stmt);
    mStream << Stmt->Operation() << '\n';
    mIndent += 2;

    PrintIndent();
    Stmt->LHS()->Accept(this);

    PrintIndent();
    Stmt->RHS()->Accept(this);

    mIndent -= 2;
  }

  void Visit(ASTBool *Stmt) override {
    ASTTypePrint("BooleanLiteral", Stmt);
    mStream << std::boolalpha << Stmt->Value() << '\n';
  }

  void Visit(ASTBreak *Stmt) override { ASTTypePrintLine("BreakStmt", Stmt); }

  void Visit(ASTChar *Stmt) override {
    ASTTypePrint("CharLiteral", Stmt);
    mStream << "'" << Stmt->Value() << "'\n";
  }

  void Visit(ASTCompound *Stmt) override {
    ASTTypePrintLine("CompoundStmt", Stmt);

    mIndent += 2;
    for (auto *S : Stmt->Stmts()) {
      PrintIndent();
      S->Accept(this);
    }
    mIndent -= 2;
  }

  void Visit(ASTContinue *Stmt) override {
    ASTTypePrintLine("ContinueStmt", Stmt);
  }

  void Visit(ASTFloat *Float) override {
    ASTTypePrint("FloatingPointLiteral", Float);
    mStream << Float->Value() << '\n';
  }

  void Visit(ASTFor *Stmt) override {
    ASTTypePrintLine("ForStmt", Stmt);

    mIndent += 2;

    if (auto *Init = Stmt->Init()) {
      PrintIndent();
      ASTTypePrintLine("ForStmtInit", Init);
      mIndent += 2;
      PrintIndent();
      Init->Accept(this);
      mIndent -= 2;
    }

    if (auto *Condition = Stmt->Condition()) {
      PrintIndent();
      ASTTypePrintLine("ForStmtCondition", Condition);
      mIndent += 2;
      PrintIndent();
      Condition->Accept(this);
      mIndent -= 2;
    }

    if (auto *Increment = Stmt->Increment()) {
      PrintIndent();
      ASTTypePrintLine("ForStmtIncrement", Increment);
      mIndent += 2;
      PrintIndent();
      Increment->Accept(this);
      mIndent -= 2;
    }

    if (auto *Body = Stmt->Body()) {
      PrintIndent();
      ASTTypePrintLine("ForStmtBody", Body);
      mIndent += 2;
      PrintIndent();
      Visit(Body);
      mIndent -= 2;
    }

    mIndent -= 2;
  }

  void Visit(ASTIf *Stmt) override {
    ASTTypePrintLine("IfStmt", Stmt);
    mIndent += 2;

    if (auto *Cond = Stmt->Condition()) {
      PrintIndent();
      ASTTypePrintLine("IfStmtCondition", Cond);
      mIndent += 2;
      PrintIndent();
      Cond->Accept(this);
      mIndent -= 2;
    }

    if (auto *Then = Stmt->ThenBody()) {
      PrintIndent();
      ASTTypePrintLine("IfStmtThenBody", Then);
      mIndent += 2;
      PrintIndent();
      Visit(Then);
      mIndent -= 2;
    }

    if (auto *Else = Stmt->ElseBody()) {
      PrintIndent();
      ASTTypePrintLine("IfStmtElseBody", Else);
      mIndent += 2;
      PrintIndent();
      Visit(Else);
      mIndent -= 2;
    }
    mIndent -= 2;
  }

  void Visit(ASTNumber *Stmt) override {
    ASTTypePrint("Number", Stmt);
    mStream << Stmt->Value() << '\n';
  }

  void Visit(ASTReturn *Stmt) override {
    ASTTypePrintLine("ReturnStmt", Stmt);

    if (auto *O = Stmt->Operand()) {
      mIndent += 2;
      PrintIndent();
      O->Accept(this);
      mIndent -= 2;
    }
  }

  void Visit(ASTString *Stmt) override {
    ASTTypePrint("StringLiteral", Stmt);
    mStream << Stmt->Value() << '\n';
  }

  void Visit(ASTSymbol *Stmt) override {
    ASTTypePrint("Symbol", Stmt);
    mStream << '`' << Stmt->Name() << "`\n";
  }

  void Visit(ASTUnary *Stmt) override {
    mStream << (
      (Stmt->PrefixOrPostfix == ASTUnary::PREFIX)
        ? "Prefix "
        : "Postfix "
    );
    ASTTypePrint("UnaryOperator", Stmt);
    mStream << Stmt->Operation() << '\n';
    mIndent += 2;

    PrintIndent();
    Stmt->Operand()->Accept(this);

    mIndent -= 2;
  }

  void Visit(ASTStructDecl *Decl) override {
    ASTTypePrint("StructDecl", Decl);
    mStream << '`' << Decl->Name() << "`\n";

    mIndent += 2;
    for (const auto &Field : Decl->Decls()) {
      PrintIndent();
      Field->Accept(this);
    }
    mIndent -= 2;
  }

  void Visit(ASTMemberAccess *Stmt) override {
    ASTTypePrintLine("StructMemberAccess", Stmt);

    mIndent += 2;
    PrintIndent();
    Stmt->Name()->Accept(this);

    PrintIndent();
    Stmt->MemberDecl()->Accept(this);
    mIndent -= 2;
  }

  void Visit(ASTVarDecl *Decl) override {
    ASTTypePrint("VarDecl", Decl);
    mStream << Decl->DataType() << ' ';
    mStream << (Decl->DataType() == DT_STRUCT ? Decl->TypeName() + ' ' : "");
    mStream << "`" << Decl->Name();
    mStream << "`\n";

    if (auto *Body = Decl->Body()) {
      mIndent += 2;
      PrintIndent();
      Body->Accept(this);
      mIndent -= 2;
    }
  }

  void Visit(ASTFunctionDecl *Decl) override {
    ASTTypePrintLine("FunctionDecl", Decl);

    mIndent += 2;
    PrintIndent();
    ASTTypePrint("FunctionDeclRetType", Decl);
    mStream << Decl->ReturnType() << '\n';

    PrintIndent();
    ASTTypePrint("FunctionDeclName", Decl);
    mStream << '`' << Decl->Name() << "`\n";

    PrintIndent();
    ASTTypePrintLine("FunctionDeclArgs", Decl);

    mIndent += 2;
    for (const auto &Argument : Decl->Args()) {
      PrintIndent();
      Argument->Accept(this);
    }
    mIndent -= 2;

    PrintIndent();
    ASTTypePrintLine("FunctionDeclBody", Decl);

    mIndent += 2;
    PrintIndent();
    Visit(Decl->Body());
    mIndent -= 2;
  }

  void Visit(ASTFunctionCall *Stmt) override {
    ASTTypePrint("FunctionCall", Stmt);
    mStream << '`' << Stmt->Name() << "`\n";

    mIndent += 2;
    PrintIndent();
    ASTTypePrintLine("FunctionCallArgs", Stmt);

    mIndent += 2;
    for (const auto &Argument : Stmt->Args()) {
      PrintIndent();
      Argument->Accept(this);
    }
    mIndent -= 2;
    mIndent -= 2;
  }

  void Visit(ASTFunctionPrototype *Stmt) override {
    ASTTypePrint("FunctionPrototype", Stmt);
    mStream << '`' << Stmt->Name() << "`\n";

    mIndent += 2;
    PrintIndent();
    ASTTypePrintLine("FunctionPrototypeArgs", Stmt);

    mIndent += 2;
    for (const auto &Argument : Stmt->Args()) {
      PrintIndent();
      Argument->Accept(this);
    }
    mIndent -= 2;

    mIndent -= 2;
  }

  void Visit(ASTDoWhile *Stmt) override {
    CommonWhileStmtVisit(Stmt, /*IsDoWhile=*/true);
  }

  void Visit(ASTWhile *Stmt) override {
    CommonWhileStmtVisit(Stmt, /*IsDoWhile=*/false);
  }

  template <typename WhileNode>
  void CommonWhileStmtVisit(WhileNode *Stmt, bool IsDoWhile) {
    std::string Prefix = IsDoWhile ? "Do" : "";

    ASTTypePrintLine(Prefix + "WhileStmt", Stmt);

    auto PrintWhileCondition = [&] {
      if (auto *Condition = Stmt->Condition()) {
        PrintIndent();
        ASTTypePrintLine(Prefix + "WhileStmtCond", Condition);
        mIndent += 2;
        PrintIndent();
        Condition->Accept(this);
        mIndent -= 2;
      }
    };

    auto PrintWhileBody = [&] {
      if (auto *Body = Stmt->Body()) {
        PrintIndent();
        ASTTypePrintLine(Prefix + "WhileStmtBody", Body);
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

  void PrintWithTextPos(std::string_view Label, ASTNode *Node, bool NewLineNeeded) const {
    mStream << Label << " <line:" << Node->LineNo();
    mStream << ", col:" << Node->ColumnNo() << ">";
    mStream << (NewLineNeeded ? '\n' : ' ');
  }

  void ASTTypePrint(std::string_view Label, ASTNode *Node) {
    PrintWithTextPos(Label, Node, false);
  }
  void ASTTypePrintLine(std::string_view Label, ASTNode *Node) {
    PrintWithTextPos(Label, Node, true);
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