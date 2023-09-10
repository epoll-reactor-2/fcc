//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:58, col:1>
//    FunctionDeclRetType <line:58, col:1> int
//    FunctionDeclName <line:58, col:1> `main`
//    FunctionDeclArgs <line:58, col:1>
//    FunctionDeclBody <line:58, col:1>
//      CompoundStmt <line:58, col:12>
//        ArrayDecl <line:59, col:3> int [1][2][3] `mem`
//        ForStmt <line:0, col:0>
//          ForStmtInit <line:60, col:8>
//            VarDecl <line:60, col:8> int `__i2`
//              Number <line:60, col:8> 0
//          ForStmtCondition <line:0, col:0>
//            BinaryOperator <line:0, col:0> <
//              Symbol <line:0, col:0> `__i2`
//              Number <line:0, col:0> 3
//          ForStmtIncrement <line:0, col:0>
//            Prefix UnaryOperator <line:0, col:0> ++
//              Symbol <line:0, col:0> `__i2`
//          ForStmtBody <line:0, col:0>
//            CompoundStmt <line:0, col:0>
//              ArrayDecl <line:0, col:0> int * [1][2] `arr1`
//              ForStmt <line:0, col:0>
//                ForStmtInit <line:61, col:10>
//                  VarDecl <line:61, col:10> int `__i3`
//                    Number <line:61, col:10> 0
//                ForStmtCondition <line:0, col:0>
//                  BinaryOperator <line:0, col:0> <
//                    Symbol <line:0, col:0> `__i3`
//                    Number <line:0, col:0> 2
//                ForStmtIncrement <line:0, col:0>
//                  Prefix UnaryOperator <line:0, col:0> ++
//                    Symbol <line:0, col:0> `__i3`
//                ForStmtBody <line:0, col:0>
//                  CompoundStmt <line:0, col:0>
//                    ArrayDecl <line:0, col:0> int * [1] `arr2`
//                    ForStmt <line:0, col:0>
//                      ForStmtInit <line:62, col:12>
//                        VarDecl <line:62, col:12> int `__i4`
//                          Number <line:62, col:12> 0
//                      ForStmtCondition <line:0, col:0>
//                        BinaryOperator <line:0, col:0> <
//                          Symbol <line:0, col:0> `__i4`
//                          Number <line:0, col:0> 1
//                      ForStmtIncrement <line:0, col:0>
//                        Prefix UnaryOperator <line:0, col:0> ++
//                          Symbol <line:0, col:0> `__i4`
//                      ForStmtBody <line:0, col:0>
//                        CompoundStmt <line:0, col:0>
//                          VarDecl <line:0, col:0> int * `i`
//                            Prefix UnaryOperator <line:0, col:0> &
//                              ArrayAccess <line:0, col:0> `arr2`
//                                Symbol <line:0, col:0> `__i4`
//                          BinaryOperator <line:63, col:12> =
//                            Prefix UnaryOperator <line:63, col:9> *
//                              Symbol <line:63, col:10> `i`
//                            Number <line:63, col:14> 666
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