//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:18, col:1>
//    FunctionDeclRetType <line:18, col:1> void
//    FunctionDeclName <line:18, col:1> `f`
//    FunctionDeclArgs <line:18, col:1>
//      VarDecl <line:18, col:8> int * `ptr`
//      VarDecl <line:18, col:18> int ** `double_ptr`
//      ArrayDecl <line:18, col:36> struct struct_type *** [2] `triple_ptr`
//    FunctionDeclBody <line:18, col:1>
//      CompoundStmt <line:18, col:66>
//        VarDecl <line:19, col:5> int * `a`
//          Number <line:19, col:14> 1
//        VarDecl <line:20, col:5> int ** `aa`
//          Number <line:20, col:16> 2
//        VarDecl <line:21, col:5> int *** `aaa`
//          Number <line:21, col:18> 3
//        ArrayDecl <line:22, col:5> int  **** [10] `aaaa`
void f(int *ptr, int **double_ptr, struct_type ***triple_ptr[2]) {
    int *a = 1;
    int **aa = 2;
    int ***aaa = 3;
    int ****aaaa[10];
}
