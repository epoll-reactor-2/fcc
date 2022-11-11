//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:26, col:1>
//    FunctionDeclRetType <line:26, col:1> <INT>
//    FunctionDeclName <line:26, col:1> `main`
//    FunctionDeclArgs <line:26, col:1>
//    FunctionDeclBody <line:26, col:1>
//      CompoundStmt <line:26, col:12>
//        ArrayDecl <line:27, col:5> <INT> [2] `array`
//        BinaryOperator <line:28, col:16> =
//          ArrayAccess <line:28, col:5> array
//            Number <line:28, col:13> 0
//          Number <line:28, col:18> 0
//        BinaryOperator <line:29, col:16> =
//          ArrayAccess <line:29, col:5> array
//            Symbol <line:29, col:11> `var`
//          Number <line:29, col:18> 1
//        FunctionCall <line:30, col:5> `function_call`
//          FunctionCallArgs <line:30, col:5>
//            ArrayAccess <line:30, col:19> array
//              Number <line:30, col:25> 0
//            ArrayAccess <line:30, col:29> array
//              Number <line:30, col:35> 1
//        ReturnStmt <line:31, col:5>
//          ArrayAccess <line:31, col:12> array
//            Number <line:31, col:18> 0
int main() {
    int array[2];
    array[  0] = 0;
    array[var] = 1;
    function_call(array[0], array[1]);
    return array[0];
}