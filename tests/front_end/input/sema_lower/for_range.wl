//CompoundStmt
//  FunctionDecl
//    FunctionDeclRetType void
//    FunctionDeclName `f`
//    FunctionDeclArgs
//      CompoundStmt
//        VarDecl int * `bc`
//    FunctionDeclBody
//      CompoundStmt
//        ArrayDecl int [2] `array`
//        ForStmt
//          ForStmtInit
//            VarDecl int `__i1`
//              Number 0
//          ForStmtCondition
//            BinaryOperator <
//              Symbol `__i1`
//              Number 2
//          ForStmtIncrement
//            Prefix UnaryOperator ++
//              Symbol `__i1`
//          ForStmtBody
//            CompoundStmt
//              VarDecl int * `i`
//                Prefix UnaryOperator &
//                  ArrayAccess `array`
//                    Symbol `__i1`
//              BinaryOperator =
//                Prefix UnaryOperator *
//                  Symbol `i`
//                Number 666
void f(int *bc) {
  //  int array[2];
  //  for (int __i = 0; __i < 2; ++__i) {
  //    int *i = &array[__i];
  //    *i = 666;
  //  }

  int array[2];
  for (int *i : array) {
    *i = 666;
  }
}