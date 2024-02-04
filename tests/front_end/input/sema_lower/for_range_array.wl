//CompoundStmt
//  FunctionDecl
//    FunctionDeclRetType int
//    FunctionDeclName `main`
//    FunctionDeclArgs
//    FunctionDeclBody
//      CompoundStmt
//        ArrayDecl int [1][2][3] `mem`
//        ForStmt
//          ForStmtInit
//            VarDecl int `__i2`
//              Number 0
//          ForStmtCondition
//            BinaryOperator <
//              Symbol `__i2`
//              Number 3
//          ForStmtIncrement
//            Prefix UnaryOperator ++
//              Symbol `__i2`
//          ForStmtBody
//            CompoundStmt
//              ArrayDecl int * [1][2] `arr1`
//                Prefix UnaryOperator &
//                  ArrayAccess `mem`
//                    Symbol `__i2`
//              ForStmt
//                ForStmtInit
//                  VarDecl int `__i3`
//                    Number 0
//                ForStmtCondition
//                  BinaryOperator <
//                    Symbol `__i3`
//                    Number 2
//                ForStmtIncrement
//                  Prefix UnaryOperator ++
//                    Symbol `__i3`
//                ForStmtBody
//                  CompoundStmt
//                    ArrayDecl int * [1] `arr2`
//                      Prefix UnaryOperator &
//                        ArrayAccess `arr1`
//                          Symbol `__i3`
//                    ForStmt
//                      ForStmtInit
//                        VarDecl int `__i4`
//                          Number 0
//                      ForStmtCondition
//                        BinaryOperator <
//                          Symbol `__i4`
//                          Number 1
//                      ForStmtIncrement
//                        Prefix UnaryOperator ++
//                          Symbol `__i4`
//                      ForStmtBody
//                        CompoundStmt
//                          VarDecl int * `i`
//                            Prefix UnaryOperator &
//                              ArrayAccess `arr2`
//                                Symbol `__i4`
//                          BinaryOperator =
//                            Prefix UnaryOperator *
//                              Symbol `i`
//                            Number 666
int main() {
  int mem[1][2][3];
  for (int *arr1[1][2] : mem) {
    for (int *arr2[1] : arr1) {
      for (int *i : arr2) {
        *i = 666;
      }
    }
  }
}