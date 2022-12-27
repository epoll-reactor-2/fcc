//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:22, col:1>
//    FunctionDeclRetType <line:22, col:1> void
//    FunctionDeclName <line:22, col:1> `f`
//    FunctionDeclArgs <line:22, col:1>
//      VarDecl <line:22, col:8> int * `ptr`
//      VarDecl <line:22, col:18> int ** `double_ptr`
//      ArrayDecl <line:22, col:36> struct struct_type *** [2] `triple_ptr`
//    FunctionDeclBody <line:22, col:1>
//      CompoundStmt <line:22, col:66>
//        VarDecl <line:23, col:5> int * `a`
//          Number <line:23, col:14> 1
//        VarDecl <line:24, col:5> int ** `aa`
//          Number <line:24, col:16> 2
//        VarDecl <line:25, col:5> int *** `aaa`
//          Number <line:25, col:18> 3
//        ArrayDecl <line:26, col:5> int  **** [10] `aaaa`
//        Prefix UnaryOperator <line:27, col:5> *
//          Symbol <line:27, col:6> `a`
//        Prefix UnaryOperator <line:28, col:5> &
//          Symbol <line:28, col:6> `a`
void f(int *ptr, int **double_ptr, struct_type ***triple_ptr[2]) {
    int *a = 1;
    int **aa = 2;
    int ***aaa = 3;
    int ****aaaa[10];
    *a;
    &a;
}
