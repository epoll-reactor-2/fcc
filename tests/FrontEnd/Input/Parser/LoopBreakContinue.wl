//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:41, col:1>
//    FunctionDeclRetType <line:41, col:1> <VOID>
//    FunctionDeclName <line:41, col:1> `f`
//    FunctionDeclArgs <line:41, col:1>
//    FunctionDeclBody <line:41, col:1>
//      CompoundStmt <line:41, col:10>
//        ForStmt <line:42, col:3>
//          ForStmtInit <line:42, col:8>
//            VarDecl <line:42, col:8> <INT> `i`
//              Number <line:42, col:16> 0
//          ForStmtCondition <line:42, col:21>
//            BinaryOperator <line:42, col:21> <
//              Symbol <line:42, col:19> `i`
//              Number <line:42, col:23> 10
//          ForStmtIncrement <line:42, col:27>
//            Prefix UnaryOperator <line:42, col:27> ++
//              Symbol <line:42, col:29> `i`
//          ForStmtBody <line:42, col:32>
//            CompoundStmt <line:42, col:32>
//              BreakStmt <line:43, col:5>
//              ContinueStmt <line:44, col:5>
//        WhileStmt <line:46, col:3>
//          WhileStmtCond <line:46, col:12>
//            BinaryOperator <line:46, col:12> <
//              Symbol <line:46, col:10> `a`
//              Symbol <line:46, col:14> `b`
//          WhileStmtBody <line:46, col:17>
//            CompoundStmt <line:46, col:17>
//              BreakStmt <line:47, col:5>
//              ContinueStmt <line:48, col:5>
//        DoWhileStmt <line:50, col:3>
//          DoWhileStmtBody <line:50, col:6>
//            CompoundStmt <line:50, col:6>
//              BreakStmt <line:51, col:5>
//              ContinueStmt <line:52, col:5>
//          DoWhileStmtCond <line:53, col:14>
//            BinaryOperator <line:53, col:14> >
//              Symbol <line:53, col:12> `b`
//              Symbol <line:53, col:16> `a`
void f() {
  for (int i = 0; i < 10; ++i) {
    break;
    continue;
  }
  while (a < b) {
    break;
    continue;
  }
  do {
    break;
    continue;
  } while (b > a);
}