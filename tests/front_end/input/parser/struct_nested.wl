//CompoundStmt <line:0, col:0>
//  StructDecl <line:32, col:1> `custom`
//    CompoundStmt <line:32, col:1>
//      VarDecl <line:33, col:5> int `a`
//      VarDecl <line:34, col:5> int `b`
//      VarDecl <line:35, col:5> int `c`
//      StructDecl <line:36, col:5> `nested`
//        CompoundStmt <line:36, col:5>
//          VarDecl <line:37, col:9> int `d`
//          VarDecl <line:38, col:9> int `e`
//          StructDecl <line:39, col:9> `nested_too_much`
//            CompoundStmt <line:39, col:9>
//              VarDecl <line:40, col:13> int `f`
//              VarDecl <line:41, col:13> int `g`
//              VarDecl <line:42, col:13> int `h`
//  FunctionDecl <line:47, col:1>
//    FunctionDeclRetType <line:47, col:1> void
//    FunctionDeclName <line:47, col:1> `f`
//    FunctionDeclArgs <line:47, col:1>
//    FunctionDeclBody <line:47, col:1>
//      CompoundStmt <line:47, col:10>
//        VarDecl <line:48, col:5> struct custom `x`
//        BinaryOperator <line:49, col:32> =
//          StructMember <line:49, col:5>
//            Symbol <line:49, col:5> `x`
//            StructMember <line:49, col:7>
//              Symbol <line:49, col:7> `nested`
//              StructMember <line:49, col:14>
//                Symbol <line:49, col:14> `nested_too_much`
//                Symbol <line:49, col:30> `f`
//          Number <line:49, col:34> 1
struct custom {
    int a;
    int b;
    int c;
    struct nested {
        int d;
        int e;
        struct nested_too_much {
            int f;
            int g;
            int h;
        };
    };
}

void f() {
    custom x;
    x.nested.nested_too_much.f = 1;
}
