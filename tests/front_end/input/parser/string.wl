//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:12, col:1>
//    FunctionDeclRetType <line:12, col:1> int
//    FunctionDeclName <line:12, col:1> `main`
//    FunctionDeclArgs <line:12, col:1>
//    FunctionDeclBody <line:12, col:1>
//      CompoundStmt <line:12, col:12>
//        VarDecl <line:13, col:5> char * `s`
//          StringLiteral <line:13, col:15> Abc
//        ReturnStmt <line:14, col:5>
//          Number <line:14, col:12> 0
int main() {
    char *s = "Abc";
    return 0;
}