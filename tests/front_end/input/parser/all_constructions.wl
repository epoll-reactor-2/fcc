//CompoundStmt <line:0, col:0>
//  StructDecl <line:74, col:1> `a`
//    CompoundStmt <line:74, col:1>
//      StructDecl <line:75, col:3> `b`
//        CompoundStmt <line:75, col:3>
//          VarDecl <line:76, col:5> int `first`
//          VarDecl <line:77, col:5> int `second`
//      VarDecl <line:79, col:3> struct b `bb`
//      VarDecl <line:80, col:3> struct a **** `aa`
//  FunctionDecl <line:83, col:1>
//    FunctionDeclRetType <line:83, col:1> int
//    FunctionDeclName <line:83, col:1> `main`
//    FunctionDeclArgs <line:83, col:1>
//    FunctionDeclBody <line:83, col:1>
//      CompoundStmt <line:83, col:12>
//        ArrayDecl <line:84, col:3> struct a ** [2] `object`
//          Number <line:84, col:19> 0
//        ArrayDecl <line:85, col:3> int ** [2] `args`
//          Number <line:85, col:19> 0
//        BinaryOperator <line:86, col:11> =
//          ArrayAccess <line:86, col:3> `args`
//            Number <line:86, col:8> 0
//          StructMember <line:86, col:14>
//            Prefix UnaryOperator <line:86, col:14> *
//              Prefix UnaryOperator <line:86, col:16> *
//                Prefix UnaryOperator <line:86, col:18> *
//                  Prefix UnaryOperator <line:86, col:20> *
//                    StructMember <line:86, col:21>
//                      Symbol <line:86, col:21> `object`
//                      Symbol <line:86, col:28> `aa`
//            StructMember <line:86, col:35>
//              Symbol <line:86, col:35> `bb`
//              Symbol <line:86, col:38> `first`
//        BinaryOperator <line:87, col:11> =
//          ArrayAccess <line:87, col:3> `args`
//            Number <line:87, col:8> 1
//          StructMember <line:87, col:14>
//            Prefix UnaryOperator <line:87, col:14> *
//              Prefix UnaryOperator <line:87, col:16> *
//                Prefix UnaryOperator <line:87, col:18> *
//                  Prefix UnaryOperator <line:87, col:20> *
//                    StructMember <line:87, col:21>
//                      Symbol <line:87, col:21> `object`
//                      Symbol <line:87, col:28> `aa`
//            StructMember <line:87, col:35>
//              Symbol <line:87, col:35> `bb`
//              Symbol <line:87, col:38> `second`
//        ReturnStmt <line:88, col:3>
//          FunctionCall <line:88, col:10> `a`
//            FunctionCallArgs <line:88, col:10>
//              CompoundStmt <line:88, col:10>
//                FunctionCall <line:88, col:12> `b`
//                  FunctionCallArgs <line:88, col:12>
//                    CompoundStmt <line:88, col:12>
//                      FunctionCall <line:88, col:14> `c`
//                        FunctionCallArgs <line:88, col:14>
//                          CompoundStmt <line:88, col:14>
//                            FunctionCall <line:88, col:16> `d`
//                              FunctionCallArgs <line:88, col:16>
//                                CompoundStmt <line:88, col:16>
//                                  FunctionCall <line:88, col:18> `e`
//                                    FunctionCallArgs <line:88, col:18>
//                                      CompoundStmt <line:88, col:18>
//                                        FunctionCall <line:88, col:20> `f`
//                                          FunctionCallArgs <line:88, col:20>
//                                            CompoundStmt <line:88, col:20>
//                                              BinaryOperator <line:88, col:32> +
//                                                Prefix UnaryOperator <line:88, col:22> ++
//                                                  ArrayAccess <line:88, col:24> `args`
//                                                    Number <line:88, col:29> 0
//                                                Prefix UnaryOperator <line:88, col:34> --
//                                                  ArrayAccess <line:88, col:36> `args`
//                                                    Number <line:88, col:41> 1
struct a {
  struct b {
    int first;
    int second;
  };
  b bb;
  a ****aa;
}

int main() {
  a **object[2] = 0;
  int **args[2] = 0;
  args[0] = (*(*(*(*object.aa)))).bb.first;
  args[1] = (*(*(*(*object.aa)))).bb.second;
  return a(b(c(d(e(f(++args[0] + --args[1]))))));
}