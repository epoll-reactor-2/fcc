//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:20, col:1>
//    FunctionDeclRetType <line:20, col:1> float
//    FunctionDeclName <line:20, col:1> `f`
//    FunctionDeclArgs <line:20, col:1>
//    FunctionDeclBody <line:20, col:1>
//      CompoundStmt <line:20, col:11>
//        ReturnStmt <line:21, col:5>
//          ImplicitCastExpr <line:21, col:14> -> float
//            BinaryOperator <line:21, col:14> +
//              Number <line:21, col:12> 1
//              BinaryOperator <line:21, col:20> +
//                FloatLiteral <line:21, col:16> 1.200000
//                ImplicitCastExpr <line:21, col:24> -> float
//                  BinaryOperator <line:21, col:24> +
//                    Number <line:21, col:22> 3
//                    BinaryOperator <line:21, col:30> +
//                      FloatLiteral <line:21, col:26> 4.500000
//                      FloatLiteral <line:21, col:32> 6.700000
float f() {
    return 1 + 1.2 + 3 + 4.5 + 6.7;
}
