//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:50, col:1>
//    FunctionDeclRetType <line:50, col:1> void
//    FunctionDeclName <line:50, col:1> `f`
//    FunctionDeclArgs <line:50, col:1>
//    FunctionDeclBody <line:50, col:1>
//      CompoundStmt <line:50, col:10>
//        ForStmt <line:51, col:3>
//          ForStmtBody <line:51, col:12>
//            CompoundStmt <line:51, col:12>
//        ForStmt <line:52, col:3>
//          ForStmtInit <line:52, col:8>
//            VarDecl <line:52, col:8> int `i`
//              Number <line:52, col:16> 0
//          ForStmtBody <line:52, col:21>
//            CompoundStmt <line:52, col:21>
//        ForStmt <line:53, col:3>
//          ForStmtCondition <line:53, col:12>
//            BinaryOperator <line:53, col:12> <
//              Symbol <line:53, col:10> `i`
//              Number <line:53, col:14> 0
//          ForStmtBody <line:53, col:18>
//            CompoundStmt <line:53, col:18>
//        ForStmt <line:54, col:3>
//          ForStmtIncrement <line:54, col:10>
//            Prefix UnaryOperator <line:54, col:10> ++
//              Symbol <line:54, col:12> `i`
//          ForStmtBody <line:54, col:15>
//            CompoundStmt <line:54, col:15>
//        ForStmt <line:55, col:3>
//          ForStmtInit <line:55, col:8>
//            VarDecl <line:55, col:8> int `i`
//              Number <line:55, col:16> 0
//          ForStmtCondition <line:55, col:21>
//            BinaryOperator <line:55, col:21> <
//              Symbol <line:55, col:19> `i`
//              Number <line:55, col:23> 10
//          ForStmtIncrement <line:55, col:29>
//            BinaryOperator <line:55, col:29> =
//              Symbol <line:55, col:27> `i`
//              BinaryOperator <line:55, col:33> *
//                Symbol <line:55, col:31> `i`
//                Number <line:55, col:35> 2
//          ForStmtBody <line:55, col:38>
//            CompoundStmt <line:55, col:38>
//              VarDecl <line:56, col:5> int `result`
//                BinaryOperator <line:56, col:20> *
//                  Symbol <line:56, col:18> `i`
//                  Number <line:56, col:22> 2
void f() {
  for (;;) {}
  for (int i = 0;;) {}
  for (; i < 0;) {}
  for (;;++i) {}
  for (int i = 0; i < 10; i = i * 2) {
    int result = i * 2;
  }
}
