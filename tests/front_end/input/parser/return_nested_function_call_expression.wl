//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:26, col:1>
//    FunctionDeclRetType <line:26, col:1> int
//    FunctionDeclName <line:26, col:1> `f`
//    FunctionDeclArgs <line:26, col:1>
//    FunctionDeclBody <line:26, col:1>
//      CompoundStmt <line:26, col:9>
//        ReturnStmt <line:27, col:3>
//          BinaryOperator <line:27, col:12> +
//            Symbol <line:27, col:10> `a`
//            FunctionCall <line:27, col:14> `b`
//              FunctionCallArgs <line:27, col:14>
//                CompoundStmt <line:27, col:14>
//                  FunctionCall <line:27, col:16> `c`
//                    FunctionCallArgs <line:27, col:16>
//                      CompoundStmt <line:27, col:16>
//                        BinaryOperator <line:27, col:20> +
//                          Number <line:27, col:18> 1
//                          BinaryOperator <line:27, col:27> +
//                            FunctionCall <line:27, col:22> `d`
//                              FunctionCallArgs <line:27, col:22>
//                                CompoundStmt <line:27, col:22>
//                                  Symbol <line:27, col:24> `e`
//                            Number <line:27, col:29> 1
//                  Symbol <line:27, col:33> `f`
int f() {
  return a + b(c(1 + d(e) + 1), f);
}
