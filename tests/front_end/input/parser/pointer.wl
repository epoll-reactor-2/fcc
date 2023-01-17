//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:27, col:1>
//    FunctionDeclRetType <line:27, col:1> void
//    FunctionDeclName <line:27, col:1> `f`
//    FunctionDeclArgs <line:27, col:1>
//      CompoundStmt <line:27, col:64>
//        VarDecl <line:27, col:8> int * `ptr`
//        VarDecl <line:27, col:18> int ** `double_ptr`
//        ArrayDecl <line:27, col:36> struct struct_type *** [2] `triple_ptr`
//    FunctionDeclBody <line:27, col:1>
//      CompoundStmt <line:27, col:66>
//        VarDecl <line:28, col:5> int * `a`
//          Number <line:28, col:14> 1
//        VarDecl <line:29, col:5> int ** `aa`
//          Number <line:29, col:16> 2
//        VarDecl <line:30, col:5> int *** `aaa`
//          Number <line:30, col:18> 3
//        ArrayDecl <line:31, col:5> int **** [10] `aaaa`
//        Prefix UnaryOperator <line:32, col:5> *
//          Symbol <line:32, col:6> `a`
//        Prefix UnaryOperator <line:33, col:5> *
//          Prefix UnaryOperator <line:33, col:6> *
//            Prefix UnaryOperator <line:33, col:7> *
//              Symbol <line:33, col:8> `a`
//        Prefix UnaryOperator <line:34, col:5> &
//          Symbol <line:34, col:6> `a`
void f(int *ptr, int **double_ptr, struct_type ***triple_ptr[2]) {
    int *a = 1;
    int **aa = 2;
    int ***aaa = 3;
    int ****aaaa[10];
    *a;
    ***a;
    &a;
}
