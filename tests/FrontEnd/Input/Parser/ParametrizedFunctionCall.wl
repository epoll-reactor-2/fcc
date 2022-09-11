//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:18, col:1>
//    FunctionDeclRetType <line:18, col:1> <VOID>
//    FunctionDeclName <line:18, col:1> f
//    FunctionDeclArgs <line:18, col:1>
//    FunctionDeclBody <line:18, col:1>
//      CompoundStmt <line:18, col:10>
//        FunctionCall <line:19, col:3> do_work
//          FunctionCallArgs <line:19, col:3>
//            IntegerLiteral <line:19, col:11> 1
//            BinaryOperator <line:19, col:24> <<
//              BinaryOperator <line:19, col:16> +
//                Symbol <line:19, col:14> a
//                BinaryOperator <line:19, col:20> *
//                  Symbol <line:19, col:18> b
//                  Symbol <line:19, col:22> c
//              IntegerLiteral <line:19, col:27> 3
void f() {
  do_work(1, a + b * c << 3);
}