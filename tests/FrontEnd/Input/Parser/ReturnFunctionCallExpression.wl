//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:15, col:1>
//    FunctionDeclRetType <line:15, col:1> int
//    FunctionDeclName <line:15, col:1> `f`
//    FunctionDeclArgs <line:15, col:1>
//    FunctionDeclBody <line:15, col:1>
//      CompoundStmt <line:15, col:9>
//        ReturnStmt <line:16, col:3>
//          BinaryOperator <line:16, col:12> +
//            Symbol <line:16, col:10> `x`
//            FunctionCall <line:16, col:14> `y`
//              FunctionCallArgs <line:16, col:14>
//                Symbol <line:16, col:16> `z`
//                Symbol <line:16, col:19> `q`
int f() {
  return x + y(z, q);
}