//CompoundStmt <line:0, col:0>
//  StructDecl <line:51, col:1> `x`
//    CompoundStmt <line:51, col:1>
//      StructDecl <line:52, col:5> `y`
//        CompoundStmt <line:52, col:5>
//          StructDecl <line:53, col:9> `z`
//            CompoundStmt <line:53, col:9>
//              VarDecl <line:54, col:13> int * `value`
//          VarDecl <line:56, col:9> struct z * `z_ptr`
//  FunctionDecl <line:60, col:1>
//    FunctionDeclRetType <line:60, col:1> int
//    FunctionDeclName <line:60, col:1> `main`
//    FunctionDeclArgs <line:60, col:1>
//    FunctionDeclBody <line:60, col:1>
//      CompoundStmt <line:60, col:12>
//        VarDecl <line:61, col:5> struct x `structure`
//        VarDecl <line:62, col:5> struct x * `ptr`
//        BinaryOperator <line:63, col:26> =
//          Prefix UnaryOperator <line:63, col:5> *
//            StructMember <line:63, col:6>
//              Symbol <line:63, col:6> `structure`
//              StructMember <line:63, col:16>
//                Symbol <line:63, col:16> `y`
//                StructMember <line:63, col:18>
//                  Symbol <line:63, col:18> `z`
//                  Symbol <line:63, col:20> `value`
//          Number <line:63, col:28> 0
//        BinaryOperator <line:64, col:23> =
//          Prefix UnaryOperator <line:64, col:5> *
//            StructMember <line:64, col:7>
//              Prefix UnaryOperator <line:64, col:7> *
//                Symbol <line:64, col:8> `ptr`
//              StructMember <line:64, col:13>
//                Symbol <line:64, col:13> `y`
//                StructMember <line:64, col:15>
//                  Symbol <line:64, col:15> `z`
//                  Symbol <line:64, col:17> `value`
//          Number <line:64, col:25> 1
//        BinaryOperator <line:65, col:30> =
//          Prefix UnaryOperator <line:65, col:5> *
//            StructMember <line:65, col:7>
//              Prefix UnaryOperator <line:65, col:7> *
//                StructMember <line:65, col:9>
//                  Prefix UnaryOperator <line:65, col:9> *
//                    Symbol <line:65, col:10> `ptr`
//                  StructMember <line:65, col:15>
//                    Symbol <line:65, col:15> `y`
//                    Symbol <line:65, col:17> `z_ptr`
//              Symbol <line:65, col:24> `value`
//          Number <line:65, col:32> 1
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
