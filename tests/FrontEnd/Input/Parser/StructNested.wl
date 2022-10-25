//CompoundStmt <line:0, col:0>
//  StructDecl <line:13, col:7> custom
//    VarDecl <line:14, col:5> <INT> a
//    VarDecl <line:15, col:5> <INT> b
//    VarDecl <line:16, col:5> <INT> c
//    StructDecl <line:17, col:11> nested
//      VarDecl <line:18, col:9> <INT> d
//      VarDecl <line:19, col:9> <INT> e
//      StructDecl <line:20, col:15> nested_too_much
//        VarDecl <line:21, col:13> <INT> f
//        VarDecl <line:22, col:13> <INT> g
//        VarDecl <line:23, col:13> <INT> h
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