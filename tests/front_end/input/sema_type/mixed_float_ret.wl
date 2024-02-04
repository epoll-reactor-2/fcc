//CompoundStmt
//  FunctionDecl
//    FunctionDeclRetType float
//    FunctionDeclName `f`
//    FunctionDeclArgs
//    FunctionDeclBody
//      CompoundStmt
//        ReturnStmt
//          ImplicitCastExpr -> float
//            BinaryOperator +
//              Number 1
//              BinaryOperator +
//                FloatLiteral 1.200000
//                ImplicitCastExpr -> float
//                  BinaryOperator +
//                    Number 3
//                    BinaryOperator +
//                      FloatLiteral 4.500000
//                      FloatLiteral 6.700000
float f() {
    return 1 + 1.2 + 3 + 4.5 + 6.7;
}
