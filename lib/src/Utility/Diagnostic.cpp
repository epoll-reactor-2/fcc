/* Diagnostic.cpp - Helper functions, used to emitting errors and warns.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "Utility/Diagnostic.h"
#include "FrontEnd/AST/ASTNode.h"

#include <sstream>

/// Forward declaration is in Diagnostic.h, so there is no unnamed namespace.
struct Diagnostic {
  enum DiagLevel { WARN, ERROR } Level;

  static void ClearBuf() { std::ostringstream().swap(ErrorStream); }

  void SetLvl(DiagLevel L) { Level = L; }

  void EmitLabel(unsigned LineNo, unsigned ColumnNo) {
    ErrorStream << ((Level == ERROR) ? "Error" : "Warning");
    ErrorStream << " at line " << LineNo << ", column " << ColumnNo << ": ";
  }

  void EmitEmptyLabel() {
    ErrorStream << ((Level == ERROR) ? "Error" : "Warning");
    ErrorStream << ": ";
  }

  static inline std::ostringstream ErrorStream, WarnStream;
};

void weak::PrintGeneratedWarns(std::ostream &Stream) {
  std::string Data = Diagnostic::WarnStream.str();
  if (!Data.empty()) {
    Stream << Data << std::flush;
    std::ostringstream().swap(Diagnostic::WarnStream);
  }
}

weak::OstreamRAII::~OstreamRAII() noexcept(false) {
  std::string Buf = DiagImpl->ErrorStream.str();

  if (DiagImpl->Level == Diagnostic::ERROR) {
    throw std::runtime_error(Buf);
  }

  Diagnostic::WarnStream << Buf << '\n';
}

std::ostream &weak::OstreamRAII::operator<<(const char *String) {
  return DiagImpl->ErrorStream << String;
}

static weak::OstreamRAII MakeMessage(Diagnostic::DiagLevel Level) {
  Diagnostic::ClearBuf();
  static Diagnostic Diag;
  Diag.SetLvl(Level);
  Diag.EmitEmptyLabel();
  return weak::OstreamRAII{&Diag};
}

static weak::OstreamRAII MakeMessage(Diagnostic::DiagLevel Level,
                                     unsigned LineNo, unsigned ColumnNo) {
  Diagnostic::ClearBuf();
  static Diagnostic Diag;
  Diag.SetLvl(Level);
  Diag.EmitLabel(LineNo, ColumnNo);
  return weak::OstreamRAII{&Diag};
}

weak::OstreamRAII weak::CompileWarning() {
  return MakeMessage(Diagnostic::WARN);
}

weak::OstreamRAII weak::CompileWarning(unsigned LineNo, unsigned ColumnNo) {
  return MakeMessage(Diagnostic::WARN, LineNo, ColumnNo);
}

weak::OstreamRAII weak::CompileWarning(const ASTNode *Node) {
  return CompileWarning(Node->LineNo(), Node->ColumnNo());
}

weak::OstreamRAII weak::CompileError() {
  return MakeMessage(Diagnostic::ERROR);
}

weak::OstreamRAII weak::CompileError(unsigned LineNo, unsigned ColumnNo) {
  return MakeMessage(Diagnostic::ERROR, LineNo, ColumnNo);
}

weak::OstreamRAII weak::CompileError(const ASTNode *Node) {
  return CompileError(Node->LineNo(), Node->ColumnNo());
}