//CompoundStmt <line:0, col:0>
//  StructDecl <line:15, col:1> `custom`
//    CompoundStmt <line:15, col:1>
//      VarDecl <line:16, col:5> int `a`
//      VarDecl <line:17, col:5> int `b`
//      VarDecl <line:18, col:5> int `c`
//      ArrayDecl <line:19, col:5> char [1000] `mem`
//      VarDecl <line:20, col:5> struct string `description`
//  FunctionProtoDecl <line:23, col:1>
//    FunctionProtoRetType <line:23, col:1> void
//    FunctionProtoName <line:23, col:1> `f`
//    FunctionProtoArgs <line:23, col:1>
//      CompoundStmt <line:23, col:21>
//        VarDecl <line:23, col:8> struct custom `record`
struct custom {
    int a;
    int b;
    int c;
    char mem[1000];
    string description;
}

void f(custom record);
