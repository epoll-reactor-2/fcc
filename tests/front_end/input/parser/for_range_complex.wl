//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:35, col:1>
//    FunctionDeclRetType <line:35, col:1> void
//    FunctionDeclName <line:35, col:1> `f`
//    FunctionDeclArgs <line:35, col:1>
//    FunctionDeclBody <line:35, col:1>
//      CompoundStmt <line:35, col:10>
//        ForRangeStmt <line:36, col:3>
//          ForRangeIterStmt <line:36, col:8>
//            VarDecl <line:36, col:8> struct structure_type `i`
//          ForRangeTargetStmt <line:36, col:27>
//            FunctionCall <line:36, col:27> `f`
//              FunctionCallArgs <line:36, col:27>
//                CompoundStmt <line:36, col:27>
//                  FunctionCall <line:36, col:29> `g`
//                    FunctionCallArgs <line:36, col:29>
//                      CompoundStmt <line:36, col:29>
//                        FunctionCall <line:36, col:31> `h`
//                          FunctionCallArgs <line:36, col:31>
//          ForRangeStmtBody <line:36, col:38>
//            CompoundStmt <line:36, col:38>
//              ForRangeStmt <line:37, col:5>
//                ForRangeIterStmt <line:37, col:10>
//                  VarDecl <line:37, col:10> struct another_type `j`
//                ForRangeTargetStmt <line:37, col:43>
//                  BinaryOperator <line:37, col:43> <<
//                    BinaryOperator <line:37, col:32> +
//                      Symbol <line:37, col:27> `this`
//                      BinaryOperator <line:37, col:37> *
//                        Symbol <line:37, col:34> `is`
//                        Symbol <line:37, col:39> `any`
//                    Symbol <line:37, col:46> `operator`
//                ForRangeStmtBody <line:37, col:56>
//                  CompoundStmt <line:37, col:56>
void f() {
  for (structure_type i : f(g(h()))) {
    for (another_type j : this + is * any << operator) {
      /* Code. */
    }
  }
}
