//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:28, col:1>
//    FunctionDeclRetType <line:28, col:1> void
//    FunctionDeclName <line:28, col:1> `f`
//    FunctionDeclArgs <line:28, col:1>
//    FunctionDeclBody <line:28, col:1>
//      CompoundStmt <line:28, col:10>
//        ForStmt <line:29, col:3>
//          ForStmtInit <line:29, col:8>
//            VarDecl <line:29, col:8> int `i`
//              Number <line:29, col:16> 0
//          ForStmtCondition <line:29, col:21>
//            BinaryOperator <line:29, col:21> <
//              Symbol <line:29, col:19> `i`
//              Number <line:29, col:23> 10
//          ForStmtIncrement <line:29, col:29>
//            BinaryOperator <line:29, col:29> =
//              Symbol <line:29, col:27> `i`
//              BinaryOperator <line:29, col:33> *
//                Symbol <line:29, col:31> `i`
//                Number <line:29, col:35> 2
//          ForStmtBody <line:29, col:38>
//            CompoundStmt <line:29, col:38>
//              VarDecl <line:30, col:5> int `result`
//                BinaryOperator <line:30, col:20> *
//                  Symbol <line:30, col:18> `i`
//                  Number <line:30, col:22> 2
void f() {
  for (int i = 0; i < 10; i = i * 2) {
    int result = i * 2;
  }
}