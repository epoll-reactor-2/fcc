/* Driver.cpp - Builder of executable code from LLVM IR.
 * Copyright (C) 2022 epoll-reactor <glibcxx.chrono@gmail.com>
 *
 * This file is distributed under the MIT license.
 */

#include "MiddleEnd/Driver/Driver.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"

namespace {

struct DriverImpl {
  DriverImpl(llvm::Module &M)
    : mIRModule(M) {
    llvm::InitializeAllTargetInfos();
    llvm::InitializeAllTargets();
    llvm::InitializeAllTargetMCs();
    llvm::InitializeAllAsmParsers();
    llvm::InitializeAllAsmPrinters();
  }

  void Build(std::string OutFile) {
    auto *TM = CreateTM(llvm::sys::getDefaultTargetTriple());
    mIRModule.setDataLayout(TM->createDataLayout());

    OutFile += ".o";
    std::error_code Errc;
    llvm::raw_fd_ostream OutStream(OutFile, Errc, llvm::sys::fs::OF_None);

    if (Errc) {
      llvm::errs() << "Could not open file: " << Errc.message();
      exit(-1);
    }

    llvm::legacy::PassManager Pass;
    TM->addPassesToEmitFile(
      Pass,
      OutStream,
      /*raw_pwrite_stream=*/nullptr,
      llvm::CGFT_ObjectFile
    );

    Pass.run(mIRModule);

    RunClangFrontEnd(OutFile);
  }

private:
  void RunClangFrontEnd(std::string_view OutFile) {
    std::string CompileCmd;
    CompileCmd += "clang++ ";
    CompileCmd += OutFile;
    CompileCmd += " -o ";
    CompileCmd += OutFile.substr(0, OutFile.size() - 2);
    system(CompileCmd.c_str());
  }

  llvm::TargetMachine *CreateTM(const std::string &Triple) {
    std::string _;
    return llvm::TargetRegistry::lookupTarget(Triple, _)
      ->createTargetMachine(
          Triple,
          /*CPU=*/"generic",
          /*Features=*/"",
          /*Opts=*/{},
          llvm::Reloc::Model::Static
        );
  }

  llvm::Module &mIRModule;
};

} // namespace

namespace weak {

Driver::Driver(llvm::Module &M, std::string_view OutPath)
  : mIRModule(M)
  , mOutPath(OutPath) {}

void Driver::Compile() {
  DriverImpl{mIRModule}.Build(mOutPath);
}

} // namespace weak