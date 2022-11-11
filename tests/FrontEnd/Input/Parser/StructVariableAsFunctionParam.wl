//CompoundStmt <line:0, col:0>
//  StructDecl <line:11, col:7> `custom`
//    VarDecl <line:12, col:5> <INT> `a`
//    VarDecl <line:13, col:5> <INT> `b`
//    VarDecl <line:14, col:5> <INT> `c`
//    ArrayDecl <line:15, col:5> <CHAR> [1000] `mem`
//    VarDecl <line:16, col:5> <STRING> `description`
//  FunctionPrototype <line:19, col:1> `f`
//    FunctionPrototypeArgs <line:19, col:1>
//      VarDecl <line:19, col:8> <STRUCT> custom `record`
struct custom {
    int a;
    int b;
    int c;
    char mem[1000];
    string description;
}

void f(custom record);