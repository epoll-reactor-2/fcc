//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:11, col:1>
//    FunctionDeclRetType <line:11, col:1> <INT>
//    FunctionDeclName <line:11, col:1> `f`
//    FunctionDeclArgs <line:11, col:1>
//    FunctionDeclBody <line:11, col:1>
//      CompoundStmt <line:11, col:9>
//        ReturnStmt <line:12, col:3>
//          FunctionCall <line:12, col:10> `call`
//            FunctionCallArgs <line:12, col:10>
int f() {
  return call();
}