//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:15, col:1>
//    FunctionDeclRetType <line:15, col:1> void
//    FunctionDeclName <line:15, col:1> `f`
//    FunctionDeclArgs <line:15, col:1>
//    FunctionDeclBody <line:15, col:1>
//      CompoundStmt <line:15, col:10>
//        ForRangeStmt <line:16, col:3>
//          ForRangeIterStmt <line:16, col:8>
//            VarDecl <line:16, col:8> int `i`
//          ForRangeTargetStmt <line:16, col:16>
//            Symbol <line:16, col:16> `array`
//          ForRangeStmtBody <line:16, col:23>
//            CompoundStmt <line:16, col:23>
void f(int *bc) {
  //  int array[2];
  //  for (int __i = 0; __i < __2; ++__i) {
  //    int *i = &array[__i];
  //  }

  int array[2];
  for (int *i : array) {}
}