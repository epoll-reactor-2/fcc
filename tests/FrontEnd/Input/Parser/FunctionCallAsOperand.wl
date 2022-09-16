//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:14, col:1>
//    FunctionDeclRetType <line:14, col:1> <INT>
//    FunctionDeclName <line:14, col:1> f
//    FunctionDeclArgs <line:14, col:1>
//    FunctionDeclBody <line:14, col:1>
//      CompoundStmt <line:14, col:9>
//        ReturnStmt <line:15, col:5>
//          BinaryOperator <line:15, col:16> ==
//            FunctionCall <line:15, col:12> x
//              FunctionCallArgs <line:15, col:12>
//            FunctionCall <line:15, col:19> y
//              FunctionCallArgs <line:15, col:19>
int f() {
    return x() == y();
}