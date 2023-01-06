//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:15, col:1>
//    FunctionDeclRetType <line:15, col:1> int
//    FunctionDeclName <line:15, col:1> `f`
//    FunctionDeclArgs <line:15, col:1>
//    FunctionDeclBody <line:15, col:1>
//      CompoundStmt <line:15, col:9>
//        ReturnStmt <line:16, col:3>
//          FunctionCall <line:16, col:10> `call`
//            FunctionCallArgs <line:16, col:10>
//              CompoundStmt <line:16, col:10>
//                Number <line:16, col:15> 1
//                Number <line:16, col:18> 2
//                Number <line:16, col:21> 3
int f() {
  return call(1, 2, 3);
}
