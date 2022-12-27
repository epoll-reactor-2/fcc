//CompoundStmt <line:0, col:0>
//  StructDecl <line:48, col:7> `x`
//    StructDecl <line:49, col:11> `y`
//      StructDecl <line:50, col:15> `z`
//        VarDecl <line:51, col:13> int * `value`
//      VarDecl <line:53, col:9> struct z * `z_ptr`
//  FunctionDecl <line:57, col:1>
//    FunctionDeclRetType <line:57, col:1> int
//    FunctionDeclName <line:57, col:1> `main`
//    FunctionDeclArgs <line:57, col:1>
//    FunctionDeclBody <line:57, col:1>
//      CompoundStmt <line:57, col:12>
//        VarDecl <line:58, col:5> struct x `structure`
//        VarDecl <line:59, col:5> struct x * `ptr`
//        BinaryOperator <line:60, col:26> =
//          Prefix UnaryOperator <line:60, col:5> *
//            StructMemberAccess <line:60, col:6>
//              Symbol <line:60, col:6> `structure`
//              StructMemberAccess <line:60, col:16>
//                Symbol <line:60, col:16> `y`
//                StructMemberAccess <line:60, col:18>
//                  Symbol <line:60, col:18> `z`
//                  Symbol <line:60, col:20> `value`
//          Number <line:60, col:28> 0
//        BinaryOperator <line:61, col:23> =
//          Prefix UnaryOperator <line:61, col:5> *
//            StructMemberAccess <line:61, col:7>
//              Prefix UnaryOperator <line:61, col:7> *
//                Symbol <line:61, col:8> `ptr`
//              StructMemberAccess <line:61, col:13>
//                Symbol <line:61, col:13> `y`
//                StructMemberAccess <line:61, col:15>
//                  Symbol <line:61, col:15> `z`
//                  Symbol <line:61, col:17> `value`
//          Number <line:61, col:25> 1
//        BinaryOperator <line:62, col:30> =
//          Prefix UnaryOperator <line:62, col:5> *
//            StructMemberAccess <line:62, col:7>
//              Prefix UnaryOperator <line:62, col:7> *
//                StructMemberAccess <line:62, col:9>
//                  Prefix UnaryOperator <line:62, col:9> *
//                    Symbol <line:62, col:10> `ptr`
//                  StructMemberAccess <line:62, col:15>
//                    Symbol <line:62, col:15> `y`
//                    Symbol <line:62, col:17> `z_ptr`
//              Symbol <line:62, col:24> `value`
//          Number <line:62, col:32> 1
struct x {
    struct y {
        struct z {
            int *value;
        };
        z *z_ptr;
    };
}

int main() {
    x structure;
    x *ptr;
    *structure.y.z.value = 0;
    *(*ptr).y.z.value = 1;
    *(*(*ptr).y.z_ptr).value = 1;
}
