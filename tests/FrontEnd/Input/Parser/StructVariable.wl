//CompoundStmt <line:0, col:0>
//  StructDecl <line:15, col:7> `custom`
//    VarDecl <line:16, col:5> int `a`
//    VarDecl <line:17, col:5> int `b`
//    VarDecl <line:18, col:5> int `c`
//    ArrayDecl <line:19, col:5> char [1000] `mem`
//    VarDecl <line:20, col:5> string `description`
//  FunctionDecl <line:23, col:1>
//    FunctionDeclRetType <line:23, col:1> void
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