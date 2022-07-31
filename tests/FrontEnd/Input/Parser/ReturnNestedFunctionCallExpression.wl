//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:23, col:1>
//    FunctionDeclRetType <line:23, col:1> <INT>
//    FunctionDeclName <line:23, col:1> f
//    FunctionDeclArgs <line:23, col:1>
//    FunctionDeclBody <line:23, col:1>
//      CompoundStmt <line:23, col:9>
//        ReturnStmt <line:24, col:3>
//          BinaryOperator <line:24, col:12> +
//            Symbol <line:24, col:10> a
//            FunctionCall <line:24, col:14> b
//              FunctionCallArgs <line:24, col:14>
//                FunctionCall <line:24, col:16> c
//                  FunctionCallArgs <line:24, col:16>
//                    BinaryOperator <line:24, col:20> +
//                      IntegerLiteral <line:24, col:18> 1
//                      BinaryOperator <line:24, col:27> +
//                        FunctionCall <line:24, col:22> d
//                          FunctionCallArgs <line:24, col:22>
//                            Symbol <line:24, col:24> e
//                        IntegerLiteral <line:24, col:29> 1
//                Symbol <line:24, col:33> f
int f() {
  return a + b(c(1 + d(e) + 1), f);
}