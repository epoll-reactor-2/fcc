#include "FrontEnd/AST/AST.h"
#include "MiddleEnd/CodeGen/TypeResolver.h"

template <typename AST, typename... ASTArgs>
void RunTest(weak::TypeResolver &TR, std::string_view Expected, ASTArgs &&...Args) {
  unsigned StubColNo = -1;
  unsigned StubLineNo = -1;

  llvm::Type *T = TR.Resolve(
    new AST(
      std::forward<ASTArgs>(Args)...,
      StubLineNo,
      StubColNo
    )
  );

  std::string TypeString;
  llvm::raw_string_ostream OS(TypeString);
  T->print(OS);

  if (TypeString == Expected)
    return;

  llvm::errs()
    << "Type mismatch:\n\t`" << TypeString
    << "` got, but\n\t`" << Expected << "` expected.\n";
  exit(-1);
}

int main() {
  using namespace weak;
  using ArrayArgs = std::vector<unsigned>;

  llvm::LLVMContext IRCtx;
  llvm::IRBuilder<> IRBuilder(IRCtx);
  TypeResolver TR(IRBuilder);

  RunTest<ASTVarDecl>(TR, "i32", DT_INT, "Name", /*PointerIndirectionLevel=*/0U, /*Body=*/nullptr);
  RunTest<ASTVarDecl>(TR, "float", DT_FLOAT, "Name", /*PointerIndirectionLevel=*/0U, /*Body=*/nullptr);
  RunTest<ASTArrayDecl>(TR, "[1 x i32]", DT_INT, "Name", ArrayArgs{ 1 }, /*PointerIndirectionLevel=*/0U);
  RunTest<ASTArrayDecl>(
    TR,
    "[1 x [2 x [3 x i32]]]",
    DT_INT,
    "Name",
    ArrayArgs{ 1, 2, 3 },
    /*PointerIndirectionLevel=*/0U
  );
  RunTest<ASTArrayDecl>(
    TR,
    "[1 x [1 x [2 x [3 x [5 x [8 x [13 x [21 x [34 x i1]]]]]]]]]",
    DT_BOOL,
    "Name",
    ArrayArgs{ 1, 1, 2, 3, 5, 8, 13, 21, 34 },
    /*PointerIndirectionLevel=*/0U
  );
}