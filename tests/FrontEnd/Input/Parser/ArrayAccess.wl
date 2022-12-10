//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:34, col:1>
//    FunctionDeclRetType <line:34, col:1> int
//    FunctionDeclName <line:34, col:1> `main`
//    FunctionDeclArgs <line:34, col:1>
//    FunctionDeclBody <line:34, col:1>
//      CompoundStmt <line:34, col:12>
//        ArrayDecl <line:35, col:5> int [2] `array`
//        BinaryOperator <line:36, col:16> =
//          ArrayAccess <line:36, col:5> array
//            Number <line:36, col:13> 0
//          Number <line:36, col:18> 0
//        BinaryOperator <line:37, col:16> =
//          ArrayAccess <line:37, col:5> array
//            Symbol <line:37, col:11> `var`
//          Number <line:37, col:18> 1
//        FunctionCall <line:38, col:5> `function_call`
//          FunctionCallArgs <line:38, col:5>
//            ArrayAccess <line:38, col:19> array
//              Number <line:38, col:25> 0
//            ArrayAccess <line:38, col:29> array
//              Number <line:38, col:35> 1
//        ReturnStmt <line:39, col:5>
//          ArrayAccess <line:39, col:12> array
//            Number <line:39, col:18> 0
//            Number <line:39, col:21> 1
//            BinaryOperator <line:39, col:26> +
//              Number <line:39, col:24> 2
//              BinaryOperator <line:39, col:34> +
//                BinaryOperator <line:39, col:30> *
//                  Number <line:39, col:28> 3
//                  Number <line:39, col:32> 4
//                Number <line:39, col:36> 5
int main() {
    int array[2];
    array[  0] = 0;
    array[var] = 1;
    function_call(array[0], array[1]);
    return array[0][1][2 + 3 * 4 + 5];
}