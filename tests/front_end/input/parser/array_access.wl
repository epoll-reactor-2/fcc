//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:44, col:1>
//    FunctionDeclRetType <line:44, col:1> int
//    FunctionDeclName <line:44, col:1> `main`
//    FunctionDeclArgs <line:44, col:1>
//    FunctionDeclBody <line:44, col:1>
//      CompoundStmt <line:44, col:12>
//        ArrayDecl <line:45, col:5> int [2] `array`
//        BinaryOperator <line:46, col:16> =
//          ArrayAccess <line:46, col:5> `array`
//            Number <line:46, col:13> 0
//          Number <line:46, col:18> 0
//        BinaryOperator <line:47, col:16> =
//          ArrayAccess <line:47, col:5> `array`
//            Symbol <line:47, col:11> `var`
//          Number <line:47, col:18> 1
//        BinaryOperator <line:48, col:19> =
//          ArrayAccess <line:48, col:5> `array`
//            Prefix UnaryOperator <line:48, col:11> *
//              Prefix UnaryOperator <line:48, col:12> *
//                Prefix UnaryOperator <line:48, col:13> *
//                  Symbol <line:48, col:14> `var`
//          Prefix UnaryOperator <line:48, col:21> *
//            Prefix UnaryOperator <line:48, col:22> *
//              Symbol <line:48, col:23> `var`
//        FunctionCall <line:49, col:5> `function_call`
//          FunctionCallArgs <line:49, col:5>
//            CompoundStmt <line:49, col:5>
//              ArrayAccess <line:49, col:19> `array`
//                Number <line:49, col:25> 0
//              ArrayAccess <line:49, col:29> `array`
//                Number <line:49, col:35> 1
//        ReturnStmt <line:50, col:5>
//          ArrayAccess <line:50, col:12> `array`
//            Number <line:50, col:18> 0
//            Number <line:50, col:21> 1
//            BinaryOperator <line:50, col:26> +
//              Number <line:50, col:24> 2
//              BinaryOperator <line:50, col:34> +
//                BinaryOperator <line:50, col:30> *
//                  Number <line:50, col:28> 3
//                  Number <line:50, col:32> 4
//                Number <line:50, col:36> 5
int main() {
    int array[2];
    array[  0] = 0;
    array[var] = 1;
    array[***var] = **var;
    function_call(array[0], array[1]);
    return array[0][1][2 + 3 * 4 + 5];
}
