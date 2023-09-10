//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:32, col:1>
//    FunctionDeclRetType <line:32, col:1> void
//    FunctionDeclName <line:32, col:1> `f`
//    FunctionDeclArgs <line:32, col:1>
//      CompoundStmt <line:32, col:15>
//        VarDecl <line:32, col:8> int * `bc`
//    FunctionDeclBody <line:32, col:1>
//      CompoundStmt <line:32, col:17>
//        ArrayDecl <line:39, col:3> int [2] `array`
//        ForStmt <line:0, col:0>
//          ForStmtInit <line:40, col:8>
//            VarDecl <line:40, col:8> int `__i1`
//              Number <line:40, col:8> 0
//          ForStmtCondition <line:0, col:0>
//            BinaryOperator <line:0, col:0> <
//              Symbol <line:0, col:0> `__i1`
//              Number <line:0, col:0> 2
//          ForStmtIncrement <line:0, col:0>
//            Prefix UnaryOperator <line:0, col:0> ++
//              Symbol <line:0, col:0> `__i1`
//          ForStmtBody <line:0, col:0>
//            CompoundStmt <line:0, col:0>
//              VarDecl <line:0, col:0> int * `i`
//                Prefix UnaryOperator <line:0, col:0> &
//                  ArrayAccess <line:0, col:0> `array`
//                    Symbol <line:0, col:0> `__i1`
//              BinaryOperator <line:41, col:8> =
//                Prefix UnaryOperator <line:41, col:5> *
//                  Symbol <line:41, col:6> `i`
//                Number <line:41, col:10> 666
void f(int *bc) {
  //  int array[2];
  //  for (int __i = 0; __i < __2; ++__i) {
  //    int *i = &array[__i];
  //    *i = 666;
  //  }

  int array[2];
  for (int *i : array) {
    *i = 666;
  }
}