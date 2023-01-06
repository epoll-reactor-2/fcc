//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:16, col:1>
//    FunctionDeclRetType <line:16, col:1> int
//    FunctionDeclName <line:16, col:1> `f`
//    FunctionDeclArgs <line:16, col:1>
//    FunctionDeclBody <line:16, col:1>
//      CompoundStmt <line:16, col:9>
//        ReturnStmt <line:17, col:3>
//          BinaryOperator <line:17, col:12> +
//            Symbol <line:17, col:10> `x`
//            FunctionCall <line:17, col:14> `y`
//              FunctionCallArgs <line:17, col:14>
//                CompoundStmt <line:17, col:14>
//                  Symbol <line:17, col:16> `z`
//                  Symbol <line:17, col:19> `q`
int f() {
  return x + y(z, q);
}
