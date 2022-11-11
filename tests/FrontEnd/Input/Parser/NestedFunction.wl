//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:19, col:1>
//    FunctionDeclRetType <line:19, col:1> <INT>
//    FunctionDeclName <line:19, col:1> `main`
//    FunctionDeclArgs <line:19, col:1>
//    FunctionDeclBody <line:19, col:1>
//      CompoundStmt <line:19, col:12>
//        FunctionDecl <line:20, col:5>
//          FunctionDeclRetType <line:20, col:5> <INT>
//          FunctionDeclName <line:20, col:5> `return_0`
//          FunctionDeclArgs <line:20, col:5>
//          FunctionDeclBody <line:20, col:5>
//            CompoundStmt <line:20, col:20>
//              ReturnStmt <line:21, col:9>
//                Number <line:21, col:16> 0
//          ReturnStmt <line:23, col:5>
//            FunctionCall <line:23, col:12> `return_0`
//              FunctionCallArgs <line:23, col:12>
int main() {
    int return_0() {
        return 0;
    }
    return return_0();
}