//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:17, col:1>
//    FunctionDeclRetType <line:17, col:1> void
//    FunctionDeclName <line:17, col:1> `f`
//    FunctionDeclArgs <line:17, col:1>
//    FunctionDeclBody <line:17, col:1>
//      CompoundStmt <line:17, col:10>
//        WhileStmt <line:18, col:3>
//          WhileStmtCond <line:18, col:12>
//            BinaryOperator <line:18, col:12> <
//              Symbol <line:18, col:10> `a`
//              Symbol <line:18, col:14> `b`
//          WhileStmtBody <line:18, col:17>
//            CompoundStmt <line:18, col:17>
//              Prefix UnaryOperator <line:19, col:5> --
//                Symbol <line:19, col:7> `a`
void f() {
  while (a < b) {
    --a;
  }
}