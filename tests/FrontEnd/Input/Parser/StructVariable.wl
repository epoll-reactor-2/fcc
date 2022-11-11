//CompoundStmt <line:0, col:0>
//  StructDecl <line:15, col:7> `custom`
//    VarDecl <line:16, col:5> <INT> `a`
//    VarDecl <line:17, col:5> <INT> `b`
//    VarDecl <line:18, col:5> <INT> `c`
//    ArrayDecl <line:19, col:5> <CHAR> [1000] `mem`
//    VarDecl <line:20, col:5> <STRING> `description`
//  FunctionDecl <line:23, col:1>
//    FunctionDeclRetType <line:23, col:1> <VOID>
//    FunctionDeclName <line:23, col:1> `f`
//    FunctionDeclArgs <line:23, col:1>
//    FunctionDeclBody <line:23, col:1>
//      CompoundStmt <line:23, col:10>
//        VarDecl <line:24, col:5> <STRUCT> custom `x`
struct custom {
    int a;
    int b;
    int c;
    char mem[1000];
    string description;
}

void f() {
    custom x;
}