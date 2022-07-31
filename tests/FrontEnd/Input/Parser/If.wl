//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:42, col:1>
//    FunctionDeclRetType <line:42, col:1> <VOID>
//    FunctionDeclName <line:42, col:1> f
//    FunctionDeclArgs <line:42, col:1>
//    FunctionDeclBody <line:42, col:1>
//      CompoundStmt <line:42, col:10>
//        IfStmt <line:43, col:3>
//          IfStmtCondition <line:43, col:7>
//            IntegerLiteral <line:43, col:7> 1
//          IfStmtThenBody <line:43, col:10>
//            CompoundStmt <line:43, col:10>
//              IfStmt <line:44, col:5>
//                IfStmtCondition <line:44, col:9>
//                  IntegerLiteral <line:44, col:9> 2
//                IfStmtThenBody <line:44, col:12>
//                  CompoundStmt <line:44, col:12>
//                    Prefix UnaryOperator <line:45, col:7> --
//                      Symbol <line:45, col:9> a
//                IfStmtElseBody <line:46, col:12>
//                  CompoundStmt <line:46, col:12>
//                    IfStmt <line:47, col:7>
//                      IfStmtCondition <line:47, col:11>
//                        IntegerLiteral <line:47, col:11> 3
//                      IfStmtThenBody <line:47, col:14>
//                        CompoundStmt <line:47, col:14>
//                          Prefix UnaryOperator <line:48, col:9> ++
//                            Symbol <line:48, col:11> b
//          IfStmtElseBody <line:51, col:10>
//            CompoundStmt <line:51, col:10>
//              IfStmt <line:52, col:5>
//                IfStmtCondition <line:52, col:9>
//                  IntegerLiteral <line:52, col:9> 4
//                IfStmtThenBody <line:52, col:12>
//                  CompoundStmt <line:52, col:12>
//                    Prefix UnaryOperator <line:53, col:7> ++
//                      Symbol <line:53, col:9> a
//                IfStmtElseBody <line:54, col:12>
//                  CompoundStmt <line:54, col:12>
//                    Prefix UnaryOperator <line:55, col:7> --
//                      Symbol <line:55, col:9> b
void f() {
  if (1) {
    if (2) {
      --a;
    } else {
      if (3) {
        ++b;
      }
    }
  } else {
    if (4) {
      ++a;
    } else {
      --b;
    }
  }
}