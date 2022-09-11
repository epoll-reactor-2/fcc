//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:33, col:1>
//    FunctionDeclRetType <line:33, col:1> <VOID>
//    FunctionDeclName <line:33, col:1> f
//    FunctionDeclArgs <line:33, col:1>
//    FunctionDeclBody <line:33, col:1>
//      CompoundStmt <line:33, col:10>
//        BinaryOperator <line:34, col:14> =
//          BinaryOperator <line:34, col:5> <<
//            Symbol <line:34, col:3> a
//            BinaryOperator <line:34, col:10> +
//              Symbol <line:34, col:8> b
//              Symbol <line:34, col:12> c
//          BinaryOperator <line:34, col:27> =
//            BinaryOperator <line:34, col:18> <<
//              Symbol <line:34, col:16> a
//              BinaryOperator <line:34, col:23> +
//                Symbol <line:34, col:21> b
//                Symbol <line:34, col:25> c
//            BinaryOperator <line:34, col:36> ==
//              BinaryOperator <line:34, col:31> <=
//                Symbol <line:34, col:29> x
//                Symbol <line:34, col:34> e
//              BinaryOperator <line:34, col:51> ==
//                BinaryOperator <line:34, col:41> >=
//                  Symbol <line:34, col:39> f
//                  BinaryOperator <line:34, col:46> <=
//                    Symbol <line:34, col:44> g
//                    Symbol <line:34, col:49> e
//                BinaryOperator <line:34, col:56> >=
//                  Symbol <line:34, col:54> f
//                  Symbol <line:34, col:59> g
void f() {
  a << b + c = a << b + c = x <= e == f >= g <= e == f >= g;
}