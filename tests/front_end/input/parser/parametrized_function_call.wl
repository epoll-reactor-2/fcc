//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:19, col:1>
//    FunctionDeclRetType <line:19, col:1> void
//    FunctionDeclName <line:19, col:1> `f`
//    FunctionDeclArgs <line:19, col:1>
//    FunctionDeclBody <line:19, col:1>
//      CompoundStmt <line:19, col:10>
//        FunctionCall <line:20, col:3> `do_work`
//          FunctionCallArgs <line:20, col:3>
//            CompoundStmt <line:20, col:3>
//              Number <line:20, col:11> 1
//              BinaryOperator <line:20, col:24> <<
//                BinaryOperator <line:20, col:16> +
//                  Symbol <line:20, col:14> `a`
//                  BinaryOperator <line:20, col:20> *
//                    Symbol <line:20, col:18> `b`
//                    Symbol <line:20, col:22> `c`
//                Number <line:20, col:27> 3
void f() {
  do_work(1, a + b * c << 3);
}
