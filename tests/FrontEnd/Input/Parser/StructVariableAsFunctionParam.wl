//CompoundStmt <line:0, col:0>
//  StructDecl <line:11, col:7> `custom`
//    VarDecl <line:12, col:5> int `a`
//    VarDecl <line:13, col:5> int `b`
//    VarDecl <line:14, col:5> int `c`
//    ArrayDecl <line:15, col:5> char [1000] `mem`
//    VarDecl <line:16, col:5> string `description`
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