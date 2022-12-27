//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:14, col:1>
//    FunctionDeclRetType <line:14, col:1> int
//    FunctionDeclName <line:14, col:1> `f`
//    FunctionDeclArgs <line:14, col:1>
//    FunctionDeclBody <line:14, col:1>
//      CompoundStmt <line:14, col:9>
//        ReturnStmt <line:15, col:3>
//          FunctionCall <line:15, col:10> `call`
//            FunctionCallArgs <line:15, col:10>
//              Number <line:15, col:15> 1
//              Number <line:15, col:18> 2
//              Number <line:15, col:21> 3
int f() {
  return call(1, 2, 3);
}