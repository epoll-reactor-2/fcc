//CompoundStmt
//  FunctionDecl
//    FunctionDeclRetType float
//    FunctionDeclName `f`
//    FunctionDeclArgs
//      CompoundStmt
//        VarDecl int `arg`
//    FunctionDeclBody
//      CompoundStmt
//        ReturnStmt
//          ImplicitCastExpr -> float
//            Number 0
//    FunctionDecl
//      FunctionDeclRetType int
//      FunctionDeclName `main`
//      FunctionDeclArgs
//      FunctionDeclBody
//        CompoundStmt
//          ReturnStmt
//            ImplicitCastExpr -> int
//              FunctionCall `f`
//                FunctionCallArgs
//                  CompoundStmt
//                    ImplicitCastExpr -> int
//                      FloatLiteral 0.000000
float f(int arg) {
    return 0;
}

int main() {
    return f(0.0);
}