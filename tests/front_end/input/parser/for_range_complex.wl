//CompoundStmt <line:0, col:0>
//  FnDecl <line:51, col:1>
//    FnDeclRetType <line:51, col:1> void
//    FnDeclName <line:51, col:1> `f`
//    FnDeclArgs <line:51, col:1>
//    FnDeclBody <line:51, col:1>
//      CompoundStmt <line:51, col:10>
//        ForRangeStmt <line:52, col:3>
//          ForRangeIterStmt <line:52, col:8>
//            VarDecl <line:52, col:8> struct structure_type `i`
//          ForRangeTargetStmt <line:52, col:27>
//            FnCall <line:52, col:27> `f`
//              FnCallArgs <line:52, col:27>
//                CompoundStmt <line:52, col:27>
//                  FnCall <line:52, col:29> `g`
//                    FnCallArgs <line:52, col:29>
//                      CompoundStmt <line:52, col:29>
//                        FnCall <line:52, col:31> `h`
//                          FnCallArgs <line:52, col:31>
//          ForRangeStmtBody <line:52, col:38>
//            CompoundStmt <line:52, col:38>
//              ForRangeStmt <line:53, col:5>
//                ForRangeIterStmt <line:53, col:10>
//                  VarDecl <line:53, col:10> struct another_type * `j`
//                ForRangeTargetStmt <line:53, col:44>
//                  BinaryOperator <line:53, col:44> <<
//                    BinaryOperator <line:53, col:33> +
//                      Symbol <line:53, col:28> `this`
//                      BinaryOperator <line:53, col:38> *
//                        Symbol <line:53, col:35> `is`
//                        Symbol <line:53, col:40> `any`
//                    Symbol <line:53, col:47> `operator`
//                ForRangeStmtBody <line:53, col:57>
//                  CompoundStmt <line:53, col:57>
//                    ForRangeStmt <line:54, col:7>
//                      ForRangeIterStmt <line:54, col:12>
//                        VarDecl <line:54, col:12> int *** `ptr`
//                      ForRangeTargetStmt <line:54, col:25>
//                        FnCall <line:54, col:25> `y`
//                          FnCallArgs <line:54, col:25>
//                      ForRangeStmtBody <line:54, col:30>
//                        CompoundStmt <line:54, col:30>
//                          ForRangeStmt <line:55, col:9>
//                            ForRangeIterStmt <line:55, col:14>
//                              ArrayDecl <line:55, col:14> int [2] `arr`
//                            ForRangeTargetStmt <line:55, col:27>
//                              FnCall <line:55, col:27> `x`
//                                FnCallArgs <line:55, col:27>
//                            ForRangeStmtBody <line:55, col:32>
//                              CompoundStmt <line:55, col:32>
void f() {
  for (structure_type i : f(g(h()))) {
    for (another_type *j : this + is * any << operator) {
      for (int ***ptr : y()) {
        for (int arr[2] : x()) {
          /* Code. */
        }
      }
    }
  }
}
