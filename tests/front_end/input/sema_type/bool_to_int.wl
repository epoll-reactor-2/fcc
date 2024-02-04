//CompoundStmt
//  FunctionDecl
//    FunctionDeclRetType boolean
//    FunctionDeclName `g`
//    FunctionDeclArgs
//    FunctionDeclBody
//      CompoundStmt
//        ReturnStmt
//          ImplicitCastExpr -> boolean
//            Number 1
bool g() {
    return 1;
}
